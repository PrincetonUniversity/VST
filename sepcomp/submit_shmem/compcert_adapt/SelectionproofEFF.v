
(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Values.
Require Import Memory.
Require Export Axioms.
Require Import Errors.
Require Import Events.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Export Maps.

Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectDiv.
Require Import SelectLong.
Require Import Selection.
Require Import SelectOpproof.
Require Import SelectDivproof.
Require Import SelectLongproof.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Import sepcomp.Cminor_coop.
Require Import sepcomp.Cminor_eff.
Require Import sepcomp.CminorSel_coop.
Require Import sepcomp.CminorSel_eff.
Require Import Floats.

(*Require Import sepcomp.Selectionproof.*)

Open Local Scope cminorsel_scope.

(** * Correctness of the instruction selection functions for expressions *)
(*
Theorem eval_addrsymbolInject: forall (ge : genv) (sp : val) (e : env) (m : mem) (le : letenv)
         (id : ident) (ofs : int) j,
       exists v : val,
         eval_expr ge sp e m le (addrsymbol id ofs) v /\
         val_inject j (symbol_address ge id ofs) v.
Proof.
  intros. unfold addrsymbol. exists (symbol_address ge id ofs); split; auto.
  destruct (symbol_is_external id).
  predSpec Int.eq Int.eq_spec ofs Int.zero.
  subst. EvalOp.
  EvalOp. econstructor. EvalOp. simpl; eauto. econstructor. simpl.
  unfold symbol_address. destruct (Genv.find_symbol ge id); auto.
  simpl. rewrite Int.add_commut. rewrite Int.add_zero. auto.
  EvalOp.
Qed.
*)

Section PRESERVATION.

Variable prog: Cminor.program.
Let ge := Genv.globalenv prog.
Variable hf: helper_functions.
Let tprog := transform_program (sel_fundef hf ge) prog.
Let tge := Genv.globalenv tprog.
Hypothesis HELPERS: i64_helpers_correct tge hf.


Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog. apply Genv.find_symbol_transf.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (sel_fundef hf ge f).
Proof.
  intros.
  exact (Genv.find_funct_ptr_transf (sel_fundef hf ge) _ _ H).
Qed.

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

(*
Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  Genv.find_funct tge v' = Some (sel_fundef hf ge f).
Proof.
  intros. inv H0.
  exact (Genv.find_funct_transf (sel_fundef hf ge) _ _ H).
  simpl in H. discriminate.
Qed.
*)

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef) j,
  Genv.find_funct ge v = Some f ->
  val_inject j v v' ->
  globalfunction_ptr_inject j ->
  Genv.find_funct tge v' = Some (sel_fundef hf ge f).
Proof.
  intros.
  exploit val_inject_function_pointer; eauto.
  intros; subst.
  exact (Genv.find_funct_transf (sel_fundef hf ge) _ _ H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (sel_fundef hf ge f) = Cminor.funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, sel_program.
  apply Genv.find_var_info_transf.
Qed.

Lemma helper_implements_preserved:
  forall id sg vargs vres,
  helper_implements ge id sg vargs vres ->
  helper_implements tge id sg vargs vres.
Proof.
  intros. destruct H as (b & ef & A & B & C & D).
  exploit function_ptr_translated; eauto. simpl. intros.
  exists b; exists ef.
  split. rewrite symbols_preserved. auto.
  split. auto.
  split. auto.
  intros. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma builtin_implements_preserved:
  forall id sg vargs vres,
  builtin_implements ge id sg vargs vres ->
  builtin_implements tge id sg vargs vres.
Proof.
  unfold builtin_implements; intros.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma helpers_correct_preserved:
  forall h, i64_helpers_correct ge h -> i64_helpers_correct tge h.
Proof.
  unfold i64_helpers_correct; intros.
  repeat (match goal with [ H: _ /\ _ |- _ /\ _ ] => destruct H; split end);
  intros; try (eapply helper_implements_preserved; eauto);
  try (eapply builtin_implements_preserved; eauto).
Qed.

Section CMCONSTR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_condexpr_of_expr:
  forall a le v b,
  eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr tge sp e m le (condexpr_of_expr a) b.
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
(* compare *)
  inv H. econstructor; eauto.
  simpl in H6. inv H6. apply Val.bool_of_val_of_optbool. auto.
(* condition *)
  inv H. econstructor; eauto. destruct va; eauto.
(* let *)
  inv H. econstructor; eauto.
(* default *)
  econstructor. constructor. eauto. constructor.
  simpl. inv H0. auto. auto.
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]].
  eapply eval_Eload; eauto.
Qed.

Lemma eval_coopstore:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  CMinSel_corestep tge (CMinSel_State f (store chunk a1 a2) k sp e) m
        (CMinSel_State f Sskip k sp e) m'.
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]].
  eapply cminsel_corestep_store; eauto.
Qed.

Lemma eval_effstore:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  cminsel_effstep tge (StoreEffect v1 (encode_val chunk v2))
        (CMinSel_State f (store chunk a1 a2) k sp e) m
        (CMinSel_State f Sskip k sp e) m'.
(*(Sstore chunk addr al b)
effsstep tge (State f (store chunk a1 a2) k sp e m)
        E0 (State f Sskip k sp e m').*)
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]].
  eapply cminsel_effstep_store; eauto.
Qed.
(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop hf op a1) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_singleoffloat; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
  eapply eval_negl; eauto.
  eapply eval_notl; eauto.
  eapply eval_intoflong; eauto.
  eapply eval_longofint; eauto.
  eapply eval_longofintu; eauto.
  eapply eval_longoffloat; eauto.
  eapply eval_longuoffloat; eauto.
  eapply eval_floatoflong; eauto.
  eapply eval_floatoflongu; eauto.
  eapply eval_singleoflong; eauto.
  eapply eval_singleoflongu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr tge sp e m le (sel_binop hf op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  eapply eval_addl; eauto.
  eapply eval_subl; eauto.
  eapply eval_mull; eauto.
  eapply eval_divl; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modl; eauto.
  eapply eval_modlu; eauto.
  eapply eval_andl; eauto.
  eapply eval_orl; eauto.
  eapply eval_xorl; eauto.
  eapply eval_shll; eauto.
  eapply eval_shrl; eauto.
  eapply eval_shrlu; eauto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
  exists v; split; auto. eapply eval_cmpl; eauto.
  exists v; split; auto. eapply eval_cmplu; eauto.
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident.
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.

Lemma classify_call_correct:
  forall sp e m a v fd,
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call ge a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  unfold classify_call; intros.
  destruct (expr_is_addrof_ident a) as [id|] eqn:?.
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H. inv H2.
  destruct (Genv.find_symbol ge id) as [b|] eqn:?.
  rewrite Genv.find_funct_find_funct_ptr in H0.
  rewrite H0.
  destruct fd. exists b; auto.
  destruct (ef_inline e0). auto. exists b; auto.
  simpl in H0. discriminate.
  auto.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

(*Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD.
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.*)

(** Lenb: replace eval_unop_lessdef with eval_unop from
    Cminorgenproof; this requires the additio of Require Import Float above
  Compatibility of [eval_unop] with respect to [val_inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  val_inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.intoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.intuoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.longoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.longuoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
Qed.

(*Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v ->
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  inv LD1. inv LD2. exists v; auto.
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
  destruct op; simpl in *; inv EV; TrivialExists.
  destruct op; try (exact H).
  simpl in *. TrivialExists. inv EV. apply Val.of_optbool_lessdef.
  intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
  intros; eapply Mem.valid_pointer_extends; eauto.
Qed.
*)
(** Lenb: same for binops
    Compatibility of [eval_binop] with respect to [val_inject]. *)

(*Lenb: fom Cminorgenproof: *)
Remark val_inject_val_of_bool:
  forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; constructor.
Qed.

(*Lenb: fom Cminorgenproof: *)
Remark val_inject_val_of_optbool:
  forall f ob, val_inject f (Val.of_optbool ob) (Val.of_optbool ob).
Proof.
  intros; destruct ob; simpl. destruct b; constructor. constructor.
Qed.

(*Lenb: fom Cminorgenproof: *)
Ltac TrivialExistsCMINORGEN :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ val_inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ val_inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vlong ?x) _ ] =>
      exists (Vlong x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.
Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  Mem.inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
      apply Int.sub_add_l.
      simpl. destruct (eq_block b1 b0); auto.
      subst b1. rewrite H in H0; inv H0.
      rewrite dec_eq_true. rewrite Int.sub_shifted. auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H. TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H. TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H. TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H. TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
    apply val_inject_val_of_optbool.
(* cmpu *)
  inv H. econstructor; split; eauto.
  unfold Val.cmpu.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  replace (Val.cmpu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  destruct b; simpl; constructor.
  symmetry. eapply val_cmpu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  simpl; auto.
(* cmpf *)
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. apply val_inject_val_of_optbool.
(* cmpl *)
  unfold Val.cmpl in *. inv H0; inv H1; simpl in H; inv H.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
(* cmplu *)
  unfold Val.cmplu in *. inv H0; inv H1; simpl in H; inv H.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
Qed.

(** * Semantic preservation for instruction selection. *)

(** Relationship between the local environments. *)
(*
Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.
*)
Definition env_inject j (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ val_inject j v1 v2.
(*
Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.
*)
Lemma set_var_inject:
  forall j e1 e2 id v1 v2,
  env_inject j e1 e2 -> val_inject j v1 v2 ->
  env_inject j (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.
(*
Lemma set_params_lessdef:
  forall il vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.
*)
Lemma set_params_inject:
  forall j il vl1 vl2,
  val_list_inject j vl1 vl2 ->
  env_inject j (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_inject; auto.
Qed.
(*
Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.*)
Lemma set_locals_inject:
  forall j e1 e2, env_inject j e1 e2 ->
  forall il, env_inject j (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_inject; auto.
Qed.

Lemma lessdef_inject: forall v j
   (Hv: forall b1, getBlocks (v::nil) b1 = true ->
                   j b1 = Some(b1,0))
   v' (LD: Val.lessdef v v'), val_inject j v v'.
Proof. intros.
  destruct v; try econstructor.
  inv LD; try constructor.
  inv LD; try constructor.
  inv LD; try constructor.
  inv LD. econstructor.
  apply Hv. rewrite getBlocks_char. exists i; left. reflexivity.
  apply eq_sym. apply Int.add_zero.
Qed.
(*
Lemma inject_lessdef: forall v j
   (Hv: forall b1, getBlocks (v::nil) b1 = true ->
                   j b1 = Some(b1,0))
   v' (INJ: val_inject j v v'), Val.lessdef v v'.
Proof. intros.
  inv INJ; try econstructor.
  rewrite (Hv b1) in H. inv H.
    rewrite Int.add_zero. constructor.
  rewrite getBlocks_char. exists ofs1; left. reflexivity.
Qed.
*)
(** Semantic preservation for expressions. *)

(*NEW*)
Definition sp_preserved (j:meminj) (sp sp':val) :=
    exists b i b', sp = Vptr b i /\ sp' = Vptr b' i /\
                j b = Some(b',0).

Lemma sel_expr_inject:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall j e' le m',
  (*Lenb: these conditions are modified*)
  env_inject j e e' -> Mem.inject j m m' ->
  (*Lenb: these conditions are new here*)
  forall (PG: meminj_preserves_globals ge j)
     (GD: genvs_domain_eq ge tge)
     (NoRepet: list_norepet (map fst (prog_defs prog)))
     sp' (SP: sp_preserved j sp sp'),
  exists v', CminorSel.eval_expr tge sp' e' m' le (sel_expr hf a) v' /\
             val_inject j v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H.
  exists (Vint i); split; auto. econstructor. constructor. auto.
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  fold (symbol_address ge i i0).
    destruct (eval_addrsymbol tge sp' e' m' le i i0) as [v' [? ?]].
    exists v'; split; trivial.
    eapply lessdef_inject; trivial. intros.
    rewrite getBlocks_char in H3. destruct H3.
    destruct H3; try contradiction.
    unfold symbol_address in H3.
    remember (Genv.find_symbol ge i) as d.
    destruct d; apply eq_sym in Heqd; inv H3.
      apply meminj_preserves_genv2blocks in PG.
      destruct PG. apply H3. unfold genv2blocks. simpl. exists i; assumption.
    unfold symbol_address in *. rewrite <- symbols_preserved. assumption.
  destruct (eval_addrstack tge sp' e' m' le i) as [v' [EV' LV']].
    exists v'; split; trivial.
    destruct SP as [b [ofs [b' [SP [SP' J]]]]]. subst.
    simpl in LV'. simpl. inv LV'.
    econstructor. eassumption. rewrite Int.add_zero. trivial.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_compat; eauto. intros [v' [C D]].
  (*WAS: exploit eval_unop_lessdef; eauto. intros [v' [C D]].*)
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto.
  inv D; inv F; try econstructor. eassumption. trivial.
  (*WAS:eapply Val.lessdef_trans; eauto. *)
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_compat; eauto. intros [v' [E F]].
  (*WAS: exploit eval_binop_lessdef; eauto. intros [v' [E F]].*)
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto.
  inv F; inv Q; try econstructor. eassumption. trivial.
  (*WAS: eapply Val.lessdef_trans; eauto. *)
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_inject; eauto. intros [v' [C D]].
  (*WAS:exploit Mem.loadv_extends; eauto. intros [v' [C D]].*)
  exists v'; split; auto. eapply eval_load; eauto.
Qed.
(*
Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr hf a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H.
  exists (Vint i); split; auto. econstructor. constructor. auto.
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  rewrite <- symbols_preserved. fold (symbol_address tge i i0). apply eval_addrsymbol.
  apply eval_addrstack.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
Qed.
*)
Lemma sel_exprlist_inject:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall j e' le m',
  (*Lenb: these conditions are modified*)
  env_inject j e e' -> Mem.inject j m m' ->
  (*Lenb: these conditions are new here*)
  forall (PG: meminj_preserves_globals ge j)
     (GD: genvs_domain_eq ge tge)
     (NoRepet: list_norepet (map fst (prog_defs prog)))
     sp' (SP: sp_preserved j sp sp'),
  exists v', CminorSel.eval_exprlist tge sp' e' m' le (sel_exprlist hf a) v' /\
             val_list_inject j v v'.
Proof.
  induction 1; intros; simpl.
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_inject; eauto. intros [v1' [A B]].
(*  exploit sel_expr_correct; eauto. intros [v1' [A B]].*)
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; eauto. constructor; eauto.
Qed.
(*
Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_exprlist tge sp e' m' le (sel_exprlist hf a) v' /\ Val.lessdef_list v v'.
Proof.
  induction 1; intros; simpl.
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_correct; eauto. intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.
*)

(** Semantic preservation for functions and statements. *)

Inductive match_cont (*NEW:*)(j:meminj): Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont j Cminor.Kstop Kstop
  | match_cont_seq: forall s k k',
      match_cont j k k' ->
      match_cont j (Cminor.Kseq s k) (Kseq (sel_stmt hf ge s) k')
  | match_cont_block: forall k k',
      match_cont j k k' ->
      match_cont j (Cminor.Kblock k) (Kblock k')
  (*sp' and sp_preserved_condition are new*)
  | match_cont_call: forall id f sp e k sp' e' k',
      match_cont j k k' ->
      (*env_lessdef e e' ->*)
      env_inject j e e' -> sp_preserved j sp sp' ->
      match_cont j (Cminor.Kcall id f sp e k) (Kcall id (sel_function hf ge f) sp' e' k').


Inductive match_states (j:meminj) : CMin_core -> mem -> CMinSel_core -> mem -> Prop :=
  | match_state: forall f s k s' k' sp e m sp' e' m',
      s' = sel_stmt hf ge s ->
      match_cont j k k' ->
      (*      env_lessdef e e' -> Mem.extends m m' ->*)
      env_inject j e e' -> Mem.inject j m m' -> sp_preserved j sp sp' ->
      match_states j
        (CMin_State f s k sp e) m
        (CMinSel_State (sel_function hf ge f) s' k' sp' e') m'
  | match_callstate: forall f args args' k k' m m',
      match_cont j k k' ->
      (*      Val.lessdef_list args args' -> Mem.extends m m' ->*)
      val_list_inject j args args' -> Mem.inject j m m' ->
      match_states j
        (CMin_Callstate f args k) m
        (CMinSel_Callstate (sel_fundef hf ge f) args' k') m'
  | match_returnstate: forall v v' k k' m m',
      match_cont j k k' ->
      (*Val.lessdef v v' -> Mem.extends m m' ->*)
      val_inject j v v' -> Mem.inject j m m' ->
      match_states j
        (CMin_Returnstate v k) m
        (CMinSel_Returnstate v' k') m'
  | match_builtin_1: forall ef args args' optid f sp e k m al sp' e' k' m',
      match_cont j k k' ->
      (*Val.lessdef_list args args' -> env_lessdef e e' -> Mem.extends m m' -> *)
      val_list_inject j args args' -> env_inject j e e' -> Mem.inject j m m' ->
      sp_preserved j sp sp' ->
      CminorSel.eval_exprlist tge sp' e' m' nil al args' ->
      match_states j
        (CMin_Callstate (External ef) args (Cminor.Kcall optid f sp e k)) m
        (CMinSel_State (sel_function hf ge f) (Sbuiltin optid ef al) k' sp' e') m'
  | match_builtin_2: forall v v' optid f sp e k m sp' e' m' k',
      match_cont j k k' ->
      (*Val.lessdef v v' -> env_lessdef e e' -> Mem.extends m m' ->*)
      val_inject j v v' -> env_inject j e e' -> Mem.inject j m m' -> sp_preserved j sp sp' ->
      match_states j
        (CMin_Returnstate v (Cminor.Kcall optid f sp e k)) m
        (CMinSel_State (sel_function hf ge f) Sskip k' sp' (set_optvar optid v' e')) m'.

Definition Match_cores (d:CMin_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Lemma env_inject_sub: forall j e e' (E: env_inject j e e')
          j' (I: inject_incr j j'), env_inject j' e e'.
Proof. intros.
  red. intros. destruct (E _ _ H) as [v2 [X Y]].
  exists v2; intuition.
  eapply val_inject_incr; eassumption.
Qed.

Lemma match_cont_sub: forall j k k' (K: match_cont j k k')
          j' (I: inject_incr j j'), match_cont j' k k'.
Proof. intros.
  induction K; try econstructor; try eassumption.
  eapply env_inject_sub; eassumption.
  destruct H0 as [b [i [b' [X [Y J]]]]].
    exists b, i, b'. apply I in J. intuition.
Qed.

Remark call_cont_commut:
  forall (*New: j*) j k k', match_cont j k k' -> match_cont j (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. constructor; auto.
Qed.

Remark find_label_commut:
  forall j lbl s k k',
  match_cont j k k' ->
  match Cminor.find_label lbl s k, find_label lbl (sel_stmt hf ge s) k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => s1' = sel_stmt hf ge s1 /\ match_cont j k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros; simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr hf e)); simpl; auto.
(* call *)
  destruct (classify_call ge e); simpl; auto.
(* tailcall *)
  destruct (classify_call ge e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)). constructor; eauto.
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt hf ge s1) (Kseq (sel_stmt hf ge s2) k')) as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* ifthenelse *)
  exploit (IHs1 k); eauto.
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt hf ge s1) k') as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* loop *)
  apply IHs. constructor; auto.
(* block *)
  apply IHs. constructor; auto.
(* return *)
  destruct o; simpl; auto.
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

(*Lenb: changed type of s from Cminor.state to CMin_core,
  adapted the constructor names,
  and removed one _ in each clause*)
Definition measure (s: CMin_core) : nat :=
  match s with
  | CMin_Callstate _ _ _ => 0%nat
  | CMin_State _ _ _ _ _ => 1%nat
  | CMin_Returnstate _ _ => 2%nat
  end.

Lemma Match_restrict: forall d mu c1 m1 c2 m2 X
          (MC: Match_cores d mu c1 m1 c2 m2)
          (HX: forall b, vis mu b = true -> X b = true)
          (RC: REACH_closed m1 X),
          Match_cores d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RCLocs [PG [GFun [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm.
  rewrite restrict_sm_all.
  rewrite restrict_nest; intuition.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RCLocs.
split. clear -PG HX Glob.
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


Lemma Match_genv: forall d mu c1 m1 c2 m2
                  (MC:Match_cores d mu c1 m1 c2 m2),
          meminj_preserves_globals ge (extern_of mu) /\
          (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
Qed.

(*FreshS/T: fresh blocks in src/tgt language*)
Definition sm_add_intern (mu: SM_Injection) j FreshS FreshT : SM_Injection :=
  Build_SM_Injection (fun b => locBlocksSrc mu b || FreshS b)
                     (fun b => locBlocksTgt mu b || FreshT b)
                     (pubBlocksSrc mu) (pubBlocksTgt mu)
                     (join (local_of mu) (fun b => match extern_of mu b with
                                             None => j b | Some _ => None end))
                     (extBlocksSrc mu) (extBlocksTgt mu)
                     (frgnBlocksSrc mu) (frgnBlocksTgt mu) (extern_of mu).

Lemma sm_add_intern_wd: forall mu j FreshS FreshT (WD: SM_wd mu)
      (HFreshS: forall b, FreshS b =true -> DomSrc mu b = false)
      (HFreshT: forall b, FreshT b =true -> DomTgt mu b = false)
      (JDomTgt: forall b1 b2 d, j b1 = Some (b2,d) ->
           as_inj mu b1 = Some(b2,d) \/
           (FreshS b1 = true /\ FreshT b2 = true)),
      SM_wd (sm_add_intern mu j FreshS FreshT).
Proof. intros.
  split; try eapply WD; eauto; intros.
destruct mu; simpl.
  remember (FreshS b) as f.
  destruct f; simpl; apply eq_sym in Heqf.
     apply HFreshS in Heqf; unfold DomSrc in Heqf; simpl in *.
     apply orb_false_iff in Heqf.
     destruct Heqf as [A B]; rewrite A, B; simpl. right; trivial.
  destruct (disjoint_extern_local_Src _ WD b); simpl in *; rewrite H; simpl.
     left; trivial. right; trivial.
destruct mu; simpl.
  remember (FreshT b) as f.
  destruct f; simpl; apply eq_sym in Heqf.
     apply HFreshT in Heqf; unfold DomTgt in Heqf; simpl in *.
     apply orb_false_iff in Heqf.
     destruct Heqf as [A B]; rewrite A, B; simpl. right; trivial.
  destruct (disjoint_extern_local_Tgt _ WD b); simpl in *; rewrite H; simpl.
     left; trivial. right; trivial.
destruct mu; simpl in *.
  remember (j b1) as d.
  destruct d; apply eq_sym in Heqd.
    destruct p.
    destruct (JDomTgt _ _ _ Heqd); simpl in *. unfold join in H.
      destruct (joinD_Some _ _ _ _ _ H0) as [EXT | [NEXT LOC]]; clear H0; simpl in *.
        destruct (disjoint_extern_local _ WD b1); simpl in H0. congruence.
        rewrite H0, EXT in H. congruence.
      rewrite LOC in H. inv H.
        destruct (local_DomRng _ WD _ _ _ LOC); simpl in *.
        rewrite H, H0. split; trivial. destruct (joinD_Some _ _ _ _ _ H) as [LOC | [NLOC X]]; clear H.
      destruct (local_DomRng _ WD _ _ _ LOC); simpl in *.
        rewrite H, H1. split; trivial.
    destruct (extern_of b1); try inv X. rewrite H1 in Heqd. inv Heqd.
      intuition.
  destruct (joinD_Some _ _ _ _ _ H).
    destruct (local_DomRng _ WD _ _ _ H0); simpl in *; clear H0.
      intuition.
    destruct H0. rewrite Heqd in H1. destruct (extern_of b1); inv H1.
simpl in *. destruct (pubSrc _ WD _ H) as [b2 [d [Hb1 Hb2]]]; simpl in *.
    exists b2, d. apply pub_in_local in Hb1.
      unfold join. rewrite Hb1, Hb2. split; trivial.
simpl in *. rewrite (pubBlocksLocalTgt _ WD _ H). intuition.
Qed.

Lemma sm_add_intern_incr: forall mu j FreshS FreshT
        (INC : inject_incr (as_inj mu) j) mu'
        (Heqmu' : mu' = sm_add_intern mu j FreshS FreshT),
     intern_incr mu mu'.
Proof. intros. subst.
  split; simpl; intuition.
  red; intros. unfold join. rewrite H. trivial.
Qed.

Lemma sm_add_intern_as_inj: forall mu j FreshS FreshT,
   as_inj (sm_add_intern mu j FreshS FreshT) =
   join (as_inj mu) (fun b => match extern_of mu b with
                              None => j b | Some _ => None end).
Proof. intros.
  extensionality b.
  destruct mu; unfold as_inj, join; simpl.
  unfold join.
  destruct (extern_of b); trivial.
    destruct p; trivial.
Qed.

Lemma sm_add_intern_incr2: forall mu j FreshS FreshT
        (INC : inject_incr (as_inj mu) j) mu'
        (Heqmu' : mu' = sm_add_intern mu j FreshS FreshT),
     inject_incr j (as_inj mu').
Proof. intros. subst. rewrite sm_add_intern_as_inj.
  red; intros. unfold join.
  remember (as_inj mu b) as d.
  destruct d; apply eq_sym in Heqd.
    destruct p. rewrite (INC _ _ _ Heqd) in H. trivial.
  destruct (joinD_None _ _ _ Heqd). rewrite H0. trivial.
Qed.

Lemma sm_add_intern_DomSrc: forall mu j FreshS FreshT,
       DomSrc (sm_add_intern mu j FreshS FreshT) = fun b => DomSrc mu b || FreshS b.
Proof. intros. extensionality b. destruct mu. unfold DomSrc; simpl.
       repeat rewrite <- orb_assoc. rewrite (orb_comm (FreshS b)). trivial.
Qed.
Lemma sm_add_intern_DomTgt: forall mu j FreshS FreshT,
       DomTgt (sm_add_intern mu j FreshS FreshT) = fun b => DomTgt mu b || FreshT b.
Proof. intros. extensionality b. destruct mu. unfold DomTgt; simpl.
       repeat rewrite <- orb_assoc. rewrite (orb_comm (FreshT b)). trivial.
Qed.

Lemma sm_add_intern_sep: forall mu j FreshS FreshT
        (HFreshS: forall b, FreshS b =true -> DomSrc mu b = false)
        (HFreshT: forall b, FreshT b =true -> DomTgt mu b = false)
        (JDomTgt: forall b1 b2 d, j b1 = Some (b2,d) ->
           as_inj mu b1 = Some(b2,d) \/
           (FreshS b1 = true /\ FreshT b2 = true))
         mu'
        (Heqmu' : mu' = sm_add_intern mu j FreshS FreshT)
        m1 m2 (WD: SM_wd mu)
        (HFreshSm1: forall b, FreshS b =true -> ~Mem.valid_block m1 b)
        (HFreshTm2: forall b, FreshT b =true -> ~Mem.valid_block m2 b),
      sm_inject_separated mu mu' m1 m2.
Proof. intros. subst.
  split; intros.
    destruct (joinD_None _ _ _ H).
    destruct (joinD_Some _ _ _ _ _ H0) as [XX | [NEXT XX]]; clear H0; simpl in *; try congruence.
    unfold join in XX. rewrite H2, H1 in XX.
    destruct (JDomTgt _ _ _ XX) as [X | [X Y]]; try congruence. intuition.
  split; intros. rewrite sm_add_intern_DomSrc in H0. rewrite H in H0; simpl in H0.
     apply HFreshSm1; trivial.
   rewrite sm_add_intern_DomTgt in H0. rewrite H in H0; simpl in H0.
     apply HFreshTm2; trivial.
Qed.

Lemma sm_add_localloc: forall mu j m1 m2 m1' m2' mu'
        (Heqmu' : mu' = sm_add_intern mu j (freshloc m1 m1') (freshloc m2 m2')),
     sm_locally_allocated mu mu' m1 m2 m1' m2'.
Proof. intros.
  rewrite sm_locally_allocatedChar.
  subst; simpl.
  rewrite sm_add_intern_DomSrc, sm_add_intern_DomTgt.
  intuition.
Qed.

Lemma Match_corestep: forall (GDE : genvs_domain_eq ge tge)
      st1 m1 st1' m1' (CS: corestep cmin_eff_sem ge st1 m1 st1' m1')
      st2 mu m2 (MC: Match_cores st1 mu st1 m1 st2 m2)
      (R: list_norepet (map fst (prog_defs prog))),
  exists st2' m2',
    (corestep_plus cminsel_eff_sem tge st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\
       corestep_star cminsel_eff_sem tge st2 m2 st2' m2')
  /\ exists mu',
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m1 m2 /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     Match_cores st1' mu' st1' m1' st2' m2' /\
     SM_wd mu' /\
     sm_valid mu' m1' m2'.
Proof.
  intros.
   inv CS; simpl in *.
  (*skip seq*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *; inv H8.
      eexists. eexists.
      split. left.
         apply corestep_plus_one.
           econstructor; eauto.
      simpl. exists mu; intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition.
  (*skip block*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists. eexists.
      split. left.
         apply corestep_plus_one.
           econstructor; eauto.
      simpl. exists mu; intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition.
  (* skip call *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      destruct H13 as [spp [i [spp' [X [X' Jsp]]]]]. inv X.
      rename spp into sp. rename spp' into sp'.
      destruct (restrictD_Some _ _ _ _ _ Jsp).
      exploit (free_parallel_inject (as_inj mu)); try eassumption. intros [m2' [A B]].
      (*WAS: exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].*)
      simpl in A. rewrite Zplus_0_r in A.
      eexists. eexists.
      split. left.
         apply corestep_plus_one.
           econstructor; eauto. inv H10; trivial.
      simpl. exists mu.
      assert (SMV': sm_valid mu m1' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      assert (RC': REACH_closed m1' (vis mu)).
        eapply REACH_closed_free; eassumption.
      intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  A).
        rewrite (freshloc_free _ _ _ _ _  H0).
        repeat split; extensionality b; intuition.
      econstructor.
        econstructor; eauto.
            eapply free_free_inject; try eassumption.
          simpl; rewrite Zplus_0_r. assumption.
        (*another proof of this Mem.inject fact is this:
            eapply inject_mapped; try eassumption.
            eapply restrict_mapped_closed; try eassumption.
            eapply inject_REACH_closed; eassumption.
            apply restrict_incr.*)
      intuition. (*
        eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Jsp).
        eapply free_free_inject; eassumption. *)
  (* assign *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto.
      (*WAS: exploit sel_expr_corect; eauto.*) intros [v' [A B]].
      eexists; eexists.
      split. left.
         apply corestep_plus_one.
           econstructor; eauto.
      simpl. exists mu. intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor.
        econstructor; trivial.
          red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
            inv H0. exists v'; auto.
            eauto.
          (*WAS:apply set_var_lessdef; auto.*)
      intuition.
  (* store *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS:exploit sel_expr_correct.*)
      exploit sel_expr_inject. eexact H. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [vaddr' [A B]].
      (*WAS: exploit sel_expr_correct.*)
      exploit sel_expr_inject. eexact H0. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [v' [C D]].
      (*WAS:exploit Mem.storev_extends; eauto. intros [m2' [P Q]].*)
      exploit Mem.storev_mapped_inject; eauto. intros [m2' [P Q]].
      eexists; eexists.
      split. left.
         apply corestep_plus_one.
            eapply eval_coopstore; eauto.
      simpl. exists mu.
      assert (SMV': sm_valid mu m1' m2').
        split; intros;
          eapply storev_valid_block_1; try eassumption;
          eapply SMV; assumption.
      intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
          try rewrite (store_freshloc _ _ _ _ _ P);
          try rewrite (store_freshloc _ _ _ _ _ H1); intuition.
      econstructor.
        econstructor; trivial.
      intuition.
      destruct vaddr; inv H1.
        eapply REACH_Store; try eassumption.
          inv B. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.
                  inv D. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
      assert (VaddrMu: val_inject (as_inj mu) vaddr vaddr').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      assert (VMu: val_inject (as_inj mu) v v').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      destruct (Mem.storev_mapped_inject _ _ _ _ _ _ _ _ _
          INJ H1 VaddrMu VMu) as [mm [Hmm1 Hmm2]].
      rewrite Hmm1 in P. inv P. assumption.
  (* Scall *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
     exploit sel_exprlist_inject; eauto.
     (*WAS: exploit sel_exprlist_correct; eauto.*) intros [vargs' [C D]].
     exploit classify_call_correct; eauto.
     destruct (classify_call ge a) as [ | id | ef].
     (* indirect *)
       exploit sel_expr_inject; eauto.
       (*exploit sel_expr_correct; eauto.*) intros [vf' [A B]].
       eexists; eexists.
       split. left.
         apply corestep_plus_one.
            econstructor. econstructor; eauto. apply C.
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption.
             apply sig_function_translated.
       simpl. exists mu. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality b;
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
         intuition.
     (* direct *)
       intros [b [U V]]. subst.
       destruct H14 as [spb [i [spb' [SP [SP' Jsp]]]]]. subst.
       assert (Jb:  restrict (as_inj mu) (vis mu) b = Some (b, 0)).
         apply meminj_preserves_genv2blocks in PGR.
         destruct PGR as [PGR1 _]. eapply PGR1.
         unfold genv2blocks. simpl. exists id; trivial.
       eexists; eexists.
       split. left. rewrite <- symbols_preserved in U.
         apply corestep_plus_one.
            econstructor. econstructor; eauto. apply C.
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption.
            apply sig_function_translated.
       simpl. exists mu. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb;
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
           exists spb, i, spb'. intuition.
         intuition.
     (* turned into Sbuiltin *)
       intros EQ. subst fd.
       eexists; eexists.
       split. right. split. omega.
           eapply corestep_star_zero.
       exists mu. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb;
           try rewrite freshloc_irrefl; intuition.
       econstructor.
         eapply match_builtin_1; try eassumption.
         intuition.
  (* Stailcall *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      assert (GFPR: globalfunction_ptr_inject (restrict (as_inj mu) (vis mu))).
            eapply restrict_GFP_vis; eassumption.
      exploit sel_expr_inject; eauto. intros [vf' [A B]].
      exploit sel_exprlist_inject; eauto. intros [vargs' [C D]].
      destruct H15 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
            apply eq_sym in X; inv X.
      destruct (restrictD_Some _ _ _ _ _ Hsp).
      exploit (free_parallel_inject (as_inj mu)); eauto. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
        exploit classify_call_correct; eauto.
        destruct (classify_call ge a) as [ | id | ef]; intros.
            econstructor. econstructor; eauto. apply C.
            eapply functions_translated; eauto.
            apply sig_function_translated.
            eassumption.
        destruct H5 as [b [U V]].
            econstructor; eauto. econstructor; eauto.
            rewrite symbols_preserved; eauto.
            eapply functions_translated; eauto. subst vf; auto.
            rewrite Genv.find_funct_find_funct_ptr in H1.
               destruct (GFPR _ _ H1).
               inv B. rewrite H9 in H5; inv H5. eauto.
            apply sig_function_translated.
        simpl. econstructor; auto. econstructor; auto.
           eassumption.
            eapply functions_translated; eauto.
            apply sig_function_translated.
       exists mu. simpl.
       assert (SMV': sm_valid mu m1' m2').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
       intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  P).
        rewrite (freshloc_free _ _ _ _ _  H3).
        repeat split; extensionality bb; intuition.
       assert (RC': REACH_closed m1' (vis mu)).
         eapply REACH_closed_free; eassumption.
       constructor.
         constructor; auto.
           apply call_cont_commut; auto.
           eapply inject_restrict; eassumption.
         intuition.
  (* Sbuiltin
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_exprlist_inject; eauto. intros [vargs' [P Q]].
      exploit external_call_mem_inject; try eapply PGR; try eassumption.
      (*WAS:exploit external_call_mem_extends; eauto. *)
      intros [j' [vres' [m2' [EXCALL2 [InjRes [Minj' [Unch1 [Unch2 [INC SEP]]]]]]]]].
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
          econstructor. eauto.
          eapply external_call_symbols_preserved; eauto.
          exact symbols_preserved. exact varinfo_preserved.
      simpl.
      remember (sm_add_intern (restrict_sm mu (vis mu)) j' (freshloc m1 m1') (freshloc m2 m2')) as mu'.
(*      exists mu'.
        assert (INC': intern_incr (restrict_sm mu (vis mu)) mu').
           eapply sm_add_intern_incr; try eassumption.
             rewrite restrict_sm_all. eassumption.
        assert (FRESHS: forall b : block, freshloc m1 m1' b = true -> DomSrc mu b = false).
          intros. apply freshloc_charT in H; destruct H.
                  remember (DomSrc mu b) as d.
                  destruct d; trivial; apply eq_sym in Heqd.
                  elim H0. apply SMV. apply Heqd.
        assert (FRESHT: forall b : block, freshloc m2 m2' b = true -> DomTgt mu b = false).
          intros. apply freshloc_charT in H; destruct H.
                  remember (DomTgt mu b) as d.
                  destruct d; trivial; apply eq_sym in Heqd.
                  elim H0. apply SMV. apply Heqd.
        assert (FRESHSR: forall b : block, freshloc m1 m1' b = true ->
                         DomSrc (restrict_sm mu (vis mu)) b = false).
                rewrite restrict_sm_DomSrc. apply FRESHS.
        assert (FRESHTR: forall b : block, freshloc m2 m2' b = true ->
                         DomTgt (restrict_sm mu (vis mu)) b = false).
                rewrite restrict_sm_DomTgt. apply FRESHT.
        assert (JJ: forall b1 b2 d, j' b1 = Some (b2, d) ->
                    as_inj (restrict_sm mu (vis mu)) b1 = Some (b2, d) \/
                    freshloc m1 m1' b1 = true /\ freshloc m2 m2' b2 = true).
          intros. remember (restrict (as_inj mu) (vis mu) b1) as q.
                 destruct q; apply eq_sym in Heqq.
                   destruct p; left. rewrite (INC _ _ _ Heqq) in H. inv H. rewrite restrict_sm_all. assumption.
                 destruct (SEP _ _ _ Heqq H).
                   right.
                   split; apply freshloc_charT; split; trivial.
                     eapply Mem.valid_block_inject_1; eassumption.
                     eapply Mem.valid_block_inject_2; eassumption.
        assert (WDR: SM_wd (restrict_sm mu (vis mu))).
                eapply restrict_sm_WD; trivial.
        assert (SEP': sm_inject_separated (restrict_sm mu (vis mu))  mu' m1 m2).
             eapply sm_add_intern_sep; try eassumption; intros.
                 apply freshloc_charT in H; eapply H.
                 apply freshloc_charT in H; eapply H.
        assert (LOCALLOC: sm_locally_allocated (restrict_sm mu (vis mu)) mu' m1 m2 m1' m2')
          by (eapply sm_add_localloc; eassumption).
   assert (WD': SM_wd mu').
     subst. eapply sm_add_intern_wd; try eassumption.
(*   assert (INCR: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
     eapply intern_incr_restrict; eassumption.
   assert (INCj': inject_incr j' (as_inj mu')).
     eapply sm_add_intern_incr2; try eassumption.*)
  assert (INCR: intern_incr mu mu').
     red; intros.
     eapply intern_incr_restrict; eassumption.
   assert (INCj': inject_incr j' (as_inj mu')).
     eapply sm_add_intern_incr2; try eassumption.*)
(*   intuition.
   split.
     constructor.
       reflexivity.
       eapply match_cont_sub; eassumption.
       destruct optid; simpl.
         eapply set_var_inject; try eassumption.
           eapply env_inject_sub; try eassumption.
           apply (val_inject_incr j'); try assumption.
             subst. red; intros. apply restrictI_Some.
               apply (INCj' _ _ _ H).
             destruct mu; unfold vis; simpl.
               destruct mu; unfold as_inj, join; simpl in *.
               destruct (JJ _ _ _ H); simpl in *.
                 destruct (joinD_Some _ _ _ _ _ H0); simpl in *.
                   rewrite H2. trivial.
                 destruct H2. unfold join. rewrite H2, H4. trivial.


         destruct optid; simpl.
          eapply set_var_inject; try eassumption.

      INC : inject_incr (as_inj mu) j'
SEP : inject_separated (as_inj mu) j' m1 m2
mu' : SM_Injection
Heqmu' : mu' = sm_add_intern mu j' (freshloc m1 m1') (freshloc m2 m2')
______________________________________(1/16)
intern_incr mu mu'
*)
(*
      exploit external_call_mem_inject; try eapply PG; try eassumption.
        eapply val_list_inject_incr; try eassumption. apply restrict_incr.
      (*WAS:exploit external_call_mem_extends; eauto. *)
      intros [j' [vres' [m2' [EXCALL2 [InjRes [Minj' [Unch1 [Unch2 [INC SEP]]]]]]]]].
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
          eapply CompCertStep_CMinSel_corestep'.
          econstructor. eauto. eapply external_call_symbols_preserved; eauto.
          exact symbols_preserved. exact varinfo_preserved.
        reflexivity. reflexivity. reflexivity.
      simpl.
      remember (sm_add_intern mu j' (freshloc m1 m1') (freshloc m2 m2')) as mu'.
      exists mu'.
        assert (INC': intern_incr mu mu') by (eapply sm_add_intern_incr; eassumption).
        assert (FRESHS: forall b : block, freshloc m1 m1' b = true -> DomSrc mu b = false).
          intros. apply freshloc_charT in H; destruct H.
                  remember (DomSrc mu b) as d.
                  destruct d; trivial; apply eq_sym in Heqd.
                  elim H0. apply SMV. apply Heqd.
        assert (FRESHT: forall b : block, freshloc m2 m2' b = true -> DomTgt mu b = false).
          intros. apply freshloc_charT in H; destruct H.
                  remember (DomTgt mu b) as d.
                  destruct d; trivial; apply eq_sym in Heqd.
                  elim H0. apply SMV. apply Heqd.
        assert (JJ: forall b1 b2 d, j' b1 = Some (b2, d) ->
                    as_inj mu b1 = Some (b2, d) \/
                    freshloc m1 m1' b1 = true /\ freshloc m2 m2' b2 = true).
          intros. remember (as_inj mu b1) as q.
                 destruct q; apply eq_sym in Heqq.
                   destruct p; left. rewrite (INC _ _ _ Heqq) in H. assumption.
                 destruct (SEP _ _ _ Heqq H).
                   right.
                   split; apply freshloc_charT; split; trivial.
                     eapply Mem.valid_block_inject_1; eassumption.
                     eapply Mem.valid_block_inject_2; eassumption.
        assert (SEP': sm_inject_separated mu mu' m1 m2).
             eapply sm_add_intern_sep; try eassumption; intros.
                 apply freshloc_charT in H; eapply H.
                 apply freshloc_charT in H; eapply H.
        assert (LOCALLOC: sm_locally_allocated mu mu' m1 m2 m1' m2')
          by (eapply sm_add_localloc; eassumption).
   assert (WD': SM_wd mu').
     subst. eapply sm_add_intern_wd; try eassumption.
   assert (INCR: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
     eapply intern_incr_restrict; eassumption.
   assert (INCj': inject_incr j' (as_inj mu')).
     eapply sm_add_intern_incr2; try eassumption.
   intuition.
   split.
     constructor.
       reflexivity.
       eapply match_cont_sub; eassumption.
       destruct optid; simpl.
         eapply set_var_inject; try eassumption.
           eapply env_inject_sub; try eassumption.
           apply (val_inject_incr j'); try assumption.
             subst. red; intros. apply restrictI_Some.
               apply (INCj' _ _ _ H).
             destruct mu; unfold vis; simpl.
               destruct mu; unfold as_inj, join; simpl in *.
               destruct (JJ _ _ _ H); simpl in *.
                 destruct (joinD_Some _ _ _ _ _ H0); simpl in *.
                   rewrite H2. trivial.
                 destruct H2. unfold join. rewrite H2, H4. trivial.


         destruct optid; simpl.
          eapply set_var_inject; try eassumption.

      INC : inject_incr (as_inj mu) j'
SEP : inject_separated (as_inj mu) j' m1 m2
mu' : SM_Injection
Heqmu' : mu' = sm_add_intern mu j' (freshloc m1 m1') (freshloc m2 m2')
______________________________________(1/16)
intern_incr mu mu'
*)
  (* can't use exists mu -- need to add the stuff new in j' . simpl.
       intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
       (*builtins as external calls?*)
      constructor; intuition.
       constructor; eauto.*)
   *)
  (* Seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [Glob [SMV [WD INJ]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality bb;
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
         intuition.
  (* Sifthenelse *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
      assert (Val.bool_of_val v' b).
        inv H0; inv B; econstructor.
      exists (CMinSel_State (sel_function hf ge f)
           (if b then sel_stmt hf ge s1 else sel_stmt hf ge s2) k' (Vptr spb' i) e').
      exists m2.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto. eapply eval_condexpr_of_expr; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. destruct b; trivial.
         exists spb, i, spb'. split; trivial. split; trivial.
       intuition.
  (* Sloop *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sblock *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sexit0_block *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sswitch *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto. intros [v' [A B]]. inv B.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
       intuition.
 (* Sreturn None *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      destruct H12 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl.
      assert (SMV': sm_valid mu m1' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto.
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
        eapply free_free_inject; try eassumption.
          simpl.  rewrite Zplus_0_r. apply P.
  (* Sreturn Some *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl.
      assert (SMV': sm_valid mu m1' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H0).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto.
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
        eapply free_free_inject; try eassumption.
          simpl. rewrite Zplus_0_r. apply P.
  (* Slabel *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
       intuition.
  (* Sgoto *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit (find_label_commut (restrict (as_inj mu) (vis mu)) lbl
              (Cminor.fn_body f) (Cminor.call_cont k)).
        apply call_cont_commut; eauto.
      rewrite H.
      destruct (find_label lbl (sel_stmt hf ge (Cminor.fn_body f)) (call_cont k'0))
          as [[s'' k'']|] eqn:?; intros; try contradiction.
      destruct H.
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
       intuition.
  (* internal function *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS: exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. intros [m2' [A B]]. *)
      exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl.
      intros [mu' [m2' [b' [Alloc' [INJ' [IntInc' [A [B C]]]]]]]].
      eexists; eexists.
      split. left.
        apply corestep_plus_one.
            econstructor; eauto.
      simpl.
      assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
      assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
      exists mu'. simpl. intuition.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H6).
         eapply restrictI_Some.
           eapply intern_incr_as_inj; eassumption.
         eapply intern_incr_vis; eassumption.
  split.
    econstructor; eauto.
      eapply match_cont_sub; try eassumption.
      eapply env_inject_sub; try eassumption.
      apply set_locals_inject. apply set_params_inject. assumption.
    eapply inject_restrict; eassumption.
    red. exists sp, Int.zero, b'. intuition.
      apply restrictI_Some; trivial. unfold vis.
      destruct (joinD_Some _ _ _ _ _ A) as [EXT | [EXT LOC]].
         assert (E: extern_of mu = extern_of mu') by eapply IntInc'.
         rewrite <- E in EXT.
         assert (DomSrc mu sp = true). eapply extern_DomRng'; eassumption.
         congruence.
      destruct (local_DomRng _ H1 _ _ _ LOC). rewrite H6; trivial.
  intuition.
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m:=m1)(tm:=m2); try eassumption.
      intros. apply as_inj_DomRng in H6.
              split; eapply SMV; eapply H6.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H6). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc'.
      apply Glob in H6. rewrite <-FF; trivial.
(* external call  no case*)
(* return *)
      destruct MC as [SMC PRE].
      inv SMC.
     inv H1.
  eexists; eexists.
    split. left. eapply corestep_plus_one.
          econstructor.
    exists mu; simpl. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition.
  (* return of an external call turned into a Sbuiltin *)
  eexists; eexists.
  split. right; split. omega.
         eapply corestep_star_zero.
  exists mu; simpl. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition.
Qed.

Lemma Match_init_cores: forall (v1 v2 : val) (sig : signature) entrypoints
  (EP: In (v1, v2, sig) entrypoints)
  (entry_points_ok : forall (v1 v2 : val) (sig : signature),
                  In (v1, v2, sig) entrypoints ->
                  exists
                    (b : Values.block) (f1 : Cminor.fundef) (f2 : fundef),
                    v1 = Vptr b Int.zero /\
                    v2 = Vptr b Int.zero /\
                    Genv.find_funct_ptr ge b = Some f1 /\
                    Genv.find_funct_ptr tge b = Some f2)
  (vals1 : list val) (c1 : CMin_core) (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (CSM_Ini :initial_core cmin_eff_sem ge v1 vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (R : list_norepet (map fst (prog_defs prog)))
  (J: forall b1 b2 d, j b1 = Some (b2, d) ->
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (InitMem : exists m0 : mem, Genv.init_mem prog = Some m0
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m1)
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))
  (GDE: genvs_domain_eq ge tge)
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b),
exists c2 : CMinSel_core,
  initial_core cminsel_eff_sem tge v2 vals2 = Some c2 /\
  Match_cores c1
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Proof. intros.
  inversion CSM_Ini.
  unfold  CMin_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0.
    apply eq_sym in Heqzz.
  exploit function_ptr_translated; eauto. intros FIND.
  exists (CMinSel_Callstate (sel_fundef hf ge f) vals2 Kstop).
  split.
  simpl.
  destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
  subst. inv A. rewrite C in Heqzz. inv Heqzz. unfold tge in FIND. rewrite D in FIND. inv FIND.
  unfold CMinSel_initial_core.
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
  solve[rewrite D; auto].
  intros CONTRA.
  solve[elimtype False; auto].
  destruct InitMem as [m0 [INIT_MEM [A B]]].
destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
    VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
   as [AA [BB [CC [DD [EE [FF GG]]]]]].
  intuition.
  split.
    eapply match_callstate.
      constructor. rewrite initial_SM_as_inj.
      unfold vis, initial_SM; simpl.
      apply forall_inject_val_list_inject.
      eapply restrict_forall_vals_inject; try eassumption.
        intros. apply REACH_nil. rewrite H; intuition.
      rewrite initial_SM_as_inj. unfold vis, initial_SM; simpl.
        eapply inject_mapped; try eassumption.
    rewrite initial_SM_as_inj in GG.
      unfold vis, initial_SM in FF; simpl in FF.
      eapply restrict_mapped_closed; eassumption.
     apply restrict_incr.
   intuition.
    rewrite match_genv_meminj_preserves_extern_iff_all. assumption.
    apply BB.
    apply EE.
    rewrite initial_SM_as_inj.
    red; intros. specialize (Genv.find_funct_ptr_not_fresh prog). intros.
         specialize (H0 _ _ _ INIT_MEM H).
         destruct (valid_init_is_global _ R _ INIT_MEM _ H0) as [id Hid].
           destruct PG as [PGa [PGb PGc]]. split. eapply PGa; eassumption.
         unfold isGlobalBlock.
          apply orb_true_iff. left. apply genv2blocksBool_char1.
            simpl. exists id; eassumption.
    rewrite initial_SM_as_inj. assumption.
Qed.

Lemma Match_eff_diagram_strong_perm:
  forall (GDE : genvs_domain_eq ge tge)
      st1 m1 st1' m1' (U1 : block -> Z -> bool)
      (CS: effstep cmin_eff_sem ge U1 st1 m1 st1' m1')
      st2 mu m2
      (EffSrc: forall b ofs, U1 b ofs = true ->
               Mem.valid_block m1 b -> vis mu b = true)
      (MC: Match_cores st1 mu st1 m1 st2 m2)
      (R: list_norepet (map fst (prog_defs prog))),
  exists st2' m2' (U2 : block -> Z -> bool),
    (effstep_plus cminsel_eff_sem tge U2 st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\
       effstep_star cminsel_eff_sem tge U2 st2 m2 st2' m2')
  /\ exists mu',
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m1 m2 /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     Match_cores st1' mu' st1' m1' st2' m2' /\
     SM_wd mu' /\
     sm_valid mu' m1' m2' /\
    (forall b2 ofs,
      U2 b2 ofs = true ->
      Mem.valid_block m2 b2 /\
      (locBlocksTgt mu b2 = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b2, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof.
  intros.
induction CS; simpl in *.
  (*skip seq*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists. eexists. eexists.
      split. left.
        apply effstep_plus_one.
          econstructor.
      simpl. exists mu; intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition.
  (*skip block*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists. eexists. eexists.
      split. left.
        apply effstep_plus_one.
          econstructor.
      simpl. exists mu; intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition.
  (* skip call *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      destruct H13 as [spp [i [spp' [X [X' Jsp]]]]]. inv X.
      rename spp into sp. rename spp' into sp'.
      destruct (restrictD_Some _ _ _ _ _ Jsp).
      exploit (free_parallel_inject (as_inj mu)); try eassumption. intros [m2' [A B]].
      (*WAS: exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].*)
      simpl in A. rewrite Zplus_0_r in A.
      eexists. eexists. eexists.
      split. left.
         apply effstep_plus_one.
           econstructor; eauto. inv H10; trivial.
      simpl. exists mu.
      assert (SMV': sm_valid mu m' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      assert (RC': REACH_closed m' (vis mu)).
        eapply REACH_closed_free; eassumption.
      intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  A).
        rewrite (freshloc_free _ _ _ _ _  H0).
        repeat split; extensionality b; intuition.
      econstructor.
        econstructor; eauto. eapply free_free_inject; try eassumption.
          simpl; rewrite Zplus_0_r. assumption.
        (*another proof of this Mem.inject fact is this:
            eapply inject_mapped; try eassumption.
            eapply restrict_mapped_closed; try eassumption.
            eapply inject_REACH_closed; eassumption.
            apply restrict_incr.*)
      intuition. (*
        eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Jsp).
        eapply free_free_inject; eassumption. *)
      eapply FreeEffect_validblock; eassumption.
      eapply FreeEffect_PropagateLeft; eassumption.
  (* assign *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto.
      (*WAS: exploit sel_expr_corect; eauto.*) intros [v' [A B]].
      eexists; eexists. eexists.
      split. left.
         apply effstep_plus_one.
           econstructor; eauto.
      simpl. exists mu. intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      split.
        econstructor; trivial.
          red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
            inv H0. exists v'; auto.
            eauto.
          (*WAS:apply set_var_lessdef; auto.*)
      intuition.
  (* store *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS:exploit sel_expr_correct.*)
      exploit sel_expr_inject. eexact H. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [vaddr' [A B]].
      (*WAS: exploit sel_expr_correct.*)
      exploit sel_expr_inject. eexact H0. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [v' [C D]].
      (*WAS:exploit Mem.storev_extends; eauto. intros [m2' [P Q]].*)
      exploit Mem.storev_mapped_inject; eauto. intros [m2' [P Q]].
      eexists; eexists. exists (StoreEffect vaddr' (encode_val chunk v')).
      split. left.
         apply effstep_plus_one.
          eapply eval_effstore; eauto.
      simpl. exists mu.
      assert (SMV': sm_valid mu m' m2').
        split; intros;
          eapply storev_valid_block_1; try eassumption;
          eapply SMV; assumption.
      intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b;
          try rewrite (store_freshloc _ _ _ _ _ P);
          try rewrite (store_freshloc _ _ _ _ _ H1); intuition.
      econstructor.
        econstructor; trivial.
      intuition.
      destruct vaddr; inv H1.
        eapply REACH_Store; try eassumption.
          inv B. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
          intros. rewrite getBlocks_char in H1. destruct H1.
                  destruct H1; try contradiction. subst.
                  inv D. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
      assert (VaddrMu: val_inject (as_inj mu) vaddr vaddr').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      assert (VMu: val_inject (as_inj mu) v v').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      destruct (Mem.storev_mapped_inject _ _ _ _ _ _ _ _ _
          INJ H1 VaddrMu VMu) as [mm [Hmm1 Hmm2]].
        rewrite Hmm1 in P. inv P. assumption.
      apply StoreEffectD in H2. destruct H2 as [i [VADDR' _]]. subst.
        simpl in P. inv B.
           eapply (Mem.valid_block_inject_2 (restrict (as_inj mu) (vis mu))); try eassumption.
           inv H1.
      eapply StoreEffect_PropagateLeft; eassumption.
  (* Scall *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
     exploit sel_exprlist_inject; eauto.
     (*WAS: exploit sel_exprlist_correct; eauto.*) intros [vargs' [C D]].
     exploit classify_call_correct; eauto.
     destruct (classify_call ge a) as [ | id | ef].
     (* indirect *)
       exploit sel_expr_inject; eauto.
       (*exploit sel_expr_correct; eauto.*) intros [vf' [A B]].
       eexists; eexists. eexists.
       split. left.
         apply effstep_plus_one.
            econstructor. econstructor; eauto. apply C.
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption.
             apply sig_function_translated.
       simpl. exists mu. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality b;
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
         intuition.
     (* direct *)
       intros [b [U V]]. subst.
       destruct H15 as [spb [i [spb' [SP [SP' Jsp]]]]]. subst.
       assert (Jb:  restrict (as_inj mu) (vis mu) b = Some (b, 0)).
         apply meminj_preserves_genv2blocks in PGR.
         destruct PGR as [PGR1 _]. eapply PGR1.
         unfold genv2blocks. simpl. exists id; trivial.
       eexists; eexists. eexists.
       split. left. rewrite <- symbols_preserved in U.
         apply effstep_plus_one.
            econstructor. econstructor; eauto. apply C.
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption.
            apply sig_function_translated.
       simpl. exists mu. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb;
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
           exists spb, i, spb'. intuition.
         intuition.
     (* turned into Sbuiltin *)
       intros EQ. subst fd.
       eexists; eexists; exists EmptyEffect.
       split. right. split. omega.
           eapply effstep_star_zero.
       exists mu. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb;
           try rewrite freshloc_irrefl; intuition.
       econstructor.
         eapply match_builtin_1; try eassumption.
         intuition.
  (* Stailcall *)
      destruct MC as [SMC PRE].
      inv SMC. simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      assert (GFPR: globalfunction_ptr_inject (restrict (as_inj mu) (vis mu))).
            eapply restrict_GFP_vis; eassumption.
      exploit sel_expr_inject; eauto. intros [vf' [A B]].
      exploit sel_exprlist_inject; eauto. intros [vargs' [C D]].
      destruct H16 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
            apply eq_sym in X; inv X.
      destruct (restrictD_Some _ _ _ _ _ Hsp).
      exploit (free_parallel_inject (as_inj mu)); eauto. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *.
      eexists; eexists. eexists.
      split. left. simpl in *.
        apply effstep_plus_one.
        exploit classify_call_correct; eauto.
        destruct (classify_call ge a) as [ | id | ef]; intros.
            econstructor. econstructor; eauto. apply C.
            eapply functions_translated; eauto.
            apply sig_function_translated.
            eassumption.
        destruct H5 as [b [U V]].
            econstructor; eauto. econstructor; eauto.
            rewrite symbols_preserved; eauto.
            eapply functions_translated; eauto. subst vf; auto.
            rewrite Genv.find_funct_find_funct_ptr in H1.
               destruct (GFPR _ _ H1).
               inv B. rewrite H9 in H5; inv H5. eauto.
            apply sig_function_translated.
        subst fd. econstructor; eauto.
           econstructor; auto. eassumption.
            eapply functions_translated; eauto.
       exists mu. simpl.
       assert (SMV': sm_valid mu m' m2').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
       intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  P).
        rewrite (freshloc_free _ _ _ _ _  H3).
        repeat split; extensionality bb; intuition.
       assert (RC': REACH_closed m' (vis mu)).
         eapply REACH_closed_free; eassumption.
       constructor.
         constructor; auto.
           apply call_cont_commut; auto.
           eapply inject_restrict; eassumption.
         intuition.
         eapply FreeEffect_validblock; eassumption.
      eapply FreeEffect_PropagateLeft; eassumption.
  (* Sbuiltin TODO, but see above , in diagram case without effects*)
  (* Seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality bb;
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
         intuition.
  (* Sifthenelse *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
      assert (Val.bool_of_val v' b).
        inv H0; inv B; econstructor.
      exists (CMinSel_State (sel_function hf ge f)
           (if b then sel_stmt hf ge s1 else sel_stmt hf ge s2) k' (Vptr spb' i) e').
      exists m2. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
            eapply eval_condexpr_of_expr; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. destruct b; trivial.
         exists spb, i, spb'. split; trivial. split; trivial.
       intuition.
  (* Sloop *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sblock *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sexit0_block *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto.
       intuition.
  (* Sswitch *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto. intros [v' [A B]]. inv B.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
       intuition.
 (* Sreturn None *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      destruct H12 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *.
      eexists; eexists. eexists.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl.
      assert (SMV': sm_valid mu m' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto.
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
        eapply free_free_inject; try eassumption.
          simpl.  rewrite Zplus_0_r. apply P.
        eapply FreeEffect_validblock; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
        eapply FreeEffect_PropagateLeft; eassumption.
  (* Sreturn Some *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *.
      eexists; eexists. eexists.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl.
      assert (SMV': sm_valid mu m' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H0).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto.
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
        eapply free_free_inject; try eassumption.
          simpl. rewrite Zplus_0_r. apply P.
        eapply FreeEffect_validblock; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
        eapply FreeEffect_PropagateLeft; eassumption.
  (* Slabel *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
       intuition.
  (* Sgoto *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit (find_label_commut (restrict (as_inj mu) (vis mu))
          lbl (Cminor.fn_body f) (Cminor.call_cont k)).
        apply call_cont_commut; eauto.
      rewrite H.
      destruct (find_label lbl (sel_stmt hf ge (Cminor.fn_body f)) (call_cont k'0))
          as [[s'' k'']|] eqn:?; intros; try contradiction.
      destruct H0.
      eexists; eexists. eexists.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      exists mu; simpl; intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
       intuition.
  (* internal function *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      (*WAS: exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. intros [m2' [A B]]. *)
      exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl.
      intros [mu' [m2' [b' [Alloc' [INJ' [IntInc' [A [B C]]]]]]]].
      eexists; eexists. eexists.
      split. left.
        apply effstep_plus_one.
            econstructor; eauto.
      simpl.
      assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
      assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
      exists mu'. simpl. intuition.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H6).
         eapply restrictI_Some.
           eapply intern_incr_as_inj; eassumption.
         eapply intern_incr_vis; eassumption.
  split.
    econstructor; eauto.
      eapply match_cont_sub; try eassumption.
      eapply env_inject_sub; try eassumption.
      apply set_locals_inject. apply set_params_inject. assumption.
    eapply inject_restrict; eassumption.
    red. exists sp, Int.zero, b'. intuition.
      apply restrictI_Some; trivial. unfold vis.
      destruct (joinD_Some _ _ _ _ _ A) as [EXT | [EXT LOC]].
         assert (E: extern_of mu = extern_of mu') by eapply IntInc'.
         rewrite <- E in EXT.
         assert (DomSrc mu sp = true). eapply extern_DomRng'; eassumption.
         congruence.
      destruct (local_DomRng _ H1 _ _ _ LOC). rewrite H6; trivial.
  intuition.
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption.
      intros. apply as_inj_DomRng in H6.
              split; eapply SMV; eapply H6.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H6). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc'.
      apply Glob in H6. rewrite <-FF; trivial.
(* no case for external calls *)
(* return *)
    destruct MC as [SMC PRE].
    inv SMC.
    inv H1.
    eexists; eexists. exists EmptyEffect.
    split. left. eapply effstep_plus_one.
          econstructor.
    exists mu; simpl. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition.
  (* return of an external call turned into a Sbuiltin *)
  eexists; eexists. exists EmptyEffect.
  split. right; split. omega.
         eapply effstep_star_zero.
  exists mu; simpl. intuition.
       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b';
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto.
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition.
(*inductive case*)
  destruct IHCS as [c2' [m2' [U2 [HH1 [mu'  HH2]]]]].
    intros. eapply EffSrc. apply H. assumption. eassumption.
    assumption. assumption.
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
Qed.

Lemma Match_AfterExternal:
forall mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
  (MemInjMu : Mem.inject (as_inj mu) m1 m2)
  (MatchMu : Match_cores st1 mu st1 m1 st2 m2)
  (AtExtSrc : at_external cmin_eff_sem st1 = Some (e, ef_sig, vals1))
  (AtExtTgt : at_external cminsel_eff_sem st2 = Some (e', ef_sig', vals2))
  (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
  (pubSrc' : Values.block -> bool)
  (pubSrcHyp : pubSrc' =
              (fun b : Values.block =>
               locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
  (pubTgt' : Values.block -> bool)
  (pubTgtHyp : pubTgt' =
              (fun b : Values.block =>
               locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
  nu
  (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
  nu' ret1 m1' ret2 m2'
  (INC : extern_incr nu nu')
  (SEP : sm_inject_separated nu nu' m1 m2)
  (WDnu' : SM_wd nu')
  (SMvalNu' : sm_valid nu' m1' m2')
  (MemInjNu' : Mem.inject (as_inj nu') m1' m2')
  (RValInjNu' : val_inject (as_inj nu') ret1 ret2)
  (FwdSrc : mem_forward m1 m1')
  (FwdTgt : mem_forward m2 m2')
  (frgnSrc' : Values.block -> bool)
  (frgnSrcHyp : frgnSrc' =
               (fun b : Values.block =>
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) &&
                REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
  (frgnTgt' : Values.block -> bool)
  (frgnTgtHyp : frgnTgt' =
               (fun b : Values.block =>
                DomTgt nu' b &&
                (negb (locBlocksTgt nu' b) &&
                 REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
  mu'
  (Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
  (UnchPrivSrc : Mem.unchanged_on
                (fun (b : Values.block) (_ : Z) =>
                 locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1
                m1')
  (UnchLOOR : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists (st1' : CMin_core) (st2' : CMinSel_core),
  after_external cmin_eff_sem (Some ret1) st1 = Some st1' /\
  after_external cminsel_eff_sem (Some ret2) st2 = Some st2' /\
  Match_cores st1' mu' st1' m1' st2' m2'.
Proof. intros.
 destruct MatchMu as [MC [RC [PG [GFP [Glob [VAL [WDmu INJ]]]]]]].
 inv MC; simpl in *; inv AtExtSrc.
 destruct f; inv H3.
  remember (sel_fundef hf ge (External e)) as tfd.
  destruct tfd; inv AtExtTgt. apply eq_sym in Heqtfd.
  exists (CMin_Returnstate ret1 k). eexists.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
  inv Heqtfd.
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
    subst. clear - INC SEP PG GFP Glob WDmu WDnu'.
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
  specialize (IHL _ H4); clear H4.
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
        apply (H2 VB) in H5.
        rewrite (H3 H5) in H7. clear H2 H3.
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
    apply andb_true_iff in H2. simpl in H2.
    destruct H2 as[DomNu' Rb'].
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
           specialize (RC' _ H2).
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
     intros. specialize (Glob _ H2).
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
  unfold vis in *.
(*  rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.*)
  econstructor; try eassumption.
    eapply match_cont_sub; try eassumption.
      rewrite (*restrict_sm_all, *)replace_externs_as_inj.
      rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc in *.
      clear RRC RR1 RC' PHnu' INCvisNu' H0 UnchLOOR UnchPrivSrc H1 H.
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
          rewrite H3, H7 in H11.
            remember (locBlocksSrc nu' b) as d.
            destruct d; trivial; simpl in *.
            apply andb_true_iff.
            split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H11). intuition.
               apply REACH_nil. unfold exportedSrc.
                 apply frgnSrc_shared in H11; trivial. rewrite H11; intuition.
      rewrite replace_externs_as_inj. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
       eapply restrict_val_inject; try eassumption.
       intros.
        destruct (getBlocks_inject (as_inj nu') (ret1::nil) (ret2::nil))
           with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
          constructor. assumption. constructor.
        remember (locBlocksSrc nu' b) as d.
        destruct d; simpl; trivial. apply andb_true_iff.
        split. eapply as_inj_DomRng; eassumption.
        apply REACH_nil. unfold exportedSrc.
           rewrite H2. trivial.
  rewrite replace_externs_as_inj.
    eapply inject_mapped; try eassumption.
      rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc.
      eapply restrict_mapped_closed; try eassumption.
unfold vis.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu'
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
intuition.
  red; intros. destruct (GFP _ _ H4). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
admit. (*CompCert issue: external builtin is inlined *)
Qed.

(*program structure not yet updated to module*)
Theorem transl_program_correct:
  forall (TRANSL: sel_program prog = OK tprog)
         (R: list_norepet (map fst (prog_defs prog)))
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
SM_simulation.SM_simulation_inject cmin_eff_sem
   cminsel_eff_sem ge tge entrypoints.
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
 eapply sepcomp.effect_simulations_lemmas.inj_simulation_star with
  (match_states:=Match_cores) (measure:=measure).
(*genvs_dom_eq*)
  assumption.
(*match_wd*)
  intros; apply H.
(*match_visible*)
  intros. apply H.
(*match_restrict*)
  apply Match_restrict.
(*match_valid*)
  intros. apply H.
(*match_genv*)
  apply Match_genv.
(*initial_core*)
  { intros.
    eapply (Match_init_cores _ _ _ entrypoints); eauto.
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
  { intros. destruct H as [MC [RC [PG [GFP [GF [VAL [WD INJ]]]]]]].
    destruct c1; inv H0. destruct k; inv H1.
    inv MC. exists v'.
    split. assumption.
    split. assumption.
    simpl. inv H1. trivial. }
(* at_external*)
  { intros. destruct H as [MC [RC [PG [GFP [Glob [VAL [WD INJ]]]]]]].
    split. inv MC; trivial.
    destruct c1; inv H0. destruct f; inv H1.
    inv MC. simpl. exists args'; intuition.
      apply val_list_inject_forall_inject; eassumption.
    simpl.
    admit. (*CompCert issue: external builtin is inlined *)
  }
(* after_external*)
  { apply Match_AfterExternal. }
(* core_diagram*)
  { intros. exploit Match_corestep; eauto.
    intros [st2' [m2' [CS2 [mu' MU']]]].
    exists st2', m2', mu'. intuition. }
(* effcore_diagram*)
  { intros. exploit Match_eff_diagram_strong_perm; eauto.
    intros [st2' [m2' [U2 [CS2 [mu' [? [? [? [? [? [? ?]]]]]]]]]]].
    exists st2', m2', mu'.
    repeat (split; try assumption).
    exists U2. split; assumption. }
Qed.


End PRESERVATION.

(*
Lemma sel_step_correct:
  forall S1 m1 S2 m2, cmin_effstep ge S1 m1 S2 m2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, cminsel_effstep tge T1 m1 T2 m2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 ME; inv ME; simpl.
  (* skip seq *)
  inv H7. left; econstructor; split. econstructor. constructor; auto.


Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, step tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 ME; inv ME; simpl.
  (* skip seq *)
  inv H7. left; econstructor; split. econstructor. constructor; auto.
  (* skip block *)
  inv H7. left; econstructor; split. econstructor. constructor; auto.
  (* skip call *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split.
  econstructor. inv H9; simpl in H; simpl; auto.
  eauto.
  constructor; auto.
  (* assign *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply set_var_lessdef; auto.
  (* store *)
  exploit sel_expr_correct. eexact H. eauto. eauto. intros [vaddr' [A B]].
  exploit sel_expr_correct. eexact H0. eauto. eauto. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  eapply eval_store; eauto.
  constructor; auto.
  (* Scall *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit classify_call_correct; eauto.
  destruct (classify_call ge a) as [ | id | ef].
  (* indirect *)
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  left; econstructor; split.
  econstructor; eauto. econstructor; eauto.
  eapply functions_translated; eauto.
  apply sig_function_translated.
  constructor; auto. constructor; auto.
  (* direct *)
  intros [b [U V]].
  left; econstructor; split.
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto.
  eapply functions_translated; eauto. subst vf; auto.
  apply sig_function_translated.
  constructor; auto. constructor; auto.
  (* turned into Sbuiltin *)
  intros EQ. subst fd.
  right; split. omega. split. auto.
  econstructor; eauto.
  (* Stailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  left; econstructor; split.
  exploit classify_call_correct; eauto.
  destruct (classify_call ge a) as [ | id | ef]; intros.
  econstructor; eauto. econstructor; eauto. eapply functions_translated; eauto. apply sig_function_translated.
  destruct H2 as [b [U V]].
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto. eapply functions_translated; eauto. subst vf; auto. apply sig_function_translated.
  econstructor; eauto. econstructor; eauto. eapply functions_translated; eauto. apply sig_function_translated.
  constructor; auto. apply call_cont_commut; auto.
  (* Sbuiltin *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
  (* Seq *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sifthenelse *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv H0.
  left; exists (State (sel_function hf ge f) (if b then sel_stmt hf ge s1 else sel_stmt hf ge s2) k' sp e' m'); split.
  econstructor; eauto. eapply eval_condexpr_of_expr; eauto.
  constructor; auto. destruct b; auto.
  (* Sloop *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sblock *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sexit seq *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* Sexit0 block *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* SexitS block *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* Sswitch *)
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split. econstructor; eauto. constructor; auto.
  (* Sreturn None *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  econstructor. simpl; eauto.
  constructor; auto. apply call_cont_commut; auto.
  (* Sreturn Some *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply call_cont_commut; auto.
  (* Slabel *)
  left; econstructor; split. constructor. constructor; auto.
  (* Sgoto *)
  exploit (find_label_commut lbl (Cminor.fn_body f) (Cminor.call_cont k)).
    apply call_cont_commut; eauto.
  rewrite H.
  destruct (find_label lbl (sel_stmt hf ge (Cminor.fn_body f)) (call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H0.
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto.
  (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m2' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply set_locals_lessdef. apply set_params_lessdef; auto.
  (* external call *)
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* external call turned into a Sbuiltin *)
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* return *)
  inv H2.
  left; econstructor; split.
  econstructor.
  constructor; auto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
  (* return of an external call turned into a Sbuiltin *)
  right; split. omega. split. auto. constructor; auto.
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  econstructor; split.
  econstructor.
  apply Genv.init_mem_transf; eauto.
  simpl. fold tge. rewrite symbols_preserved. eexact H0.
  apply function_ptr_translated. eauto.
  rewrite <- H2. apply sig_function_translated; auto.
  constructor; auto. constructor. apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv H3. inv H5. constructor.
Qed.

End PRESERVATION.

Axiom get_helpers_correct:
  forall ge hf, get_helpers ge = OK hf -> i64_helpers_correct ge hf.

Theorem transf_program_correct:
  forall prog tprog,
  sel_program prog = OK tprog ->
  forward_simulation (Cminor.semantics prog) (CminorSel.semantics tprog).
Proof.
  intros. unfold sel_program in H.
  destruct (get_helpers (Genv.globalenv prog)) as [hf|] eqn:E; simpl in H; try discriminate.
  inv H.
  eapply forward_simulation_opt.
  apply symbols_preserved.
  apply sel_initial_states.
  apply sel_final_states.
  apply sel_step_correct. apply helpers_correct_preserved. apply get_helpers_correct. auto.
Qed.
*)