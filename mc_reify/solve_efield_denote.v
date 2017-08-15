Require Import VST.floyd.proofauto.
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Require Export mc_reify.reify.
Require Import mc_reify.set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.
Require Import mc_reify.typ_eq.
Require Import mc_reify.rtac_base.

Lemma msubst_efield_denote_nil: forall T1 T2, msubst_efield_denote T1 T2 nil = Some nil.
Proof.
  intros.
  reflexivity.
Qed.

Lemma msubst_efield_denote_cons_struct: forall fld efs T1 T2 gfs,
  msubst_efield_denote T1 T2 efs = Some gfs ->
  msubst_efield_denote T1 T2 (eStructField fld :: efs) = Some (StructField fld :: gfs).
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma msubst_efield_denote_cons_union: forall fld efs T1 T2 gfs,
  msubst_efield_denote T1 T2 efs = Some gfs ->
  msubst_efield_denote T1 T2 (eUnionField fld :: efs) = Some (UnionField fld :: gfs).
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma msubst_efield_denote_cons_array: forall ei efs T1 T2 i gfs,
  msubst_efield_denote T1 T2 efs = Some gfs ->
  type_is_int ei = true ->
  msubst_eval_LR T1 T2 ei RRRR = Some (Values.Vint i) ->
  msubst_efield_denote T1 T2 (eArraySubsc ei :: efs) = Some (ArraySubsc (Int.unsigned i) :: gfs).
Proof.
  intros.
  simpl.
  unfold type_is_int in H0.
  destruct (typeof ei); try inversion H0.
  unfold msubst_eval_LR in H1.
  rewrite H, H1.
  reflexivity.
Qed.

(************************************************

Reified Lemmas

************************************************)

Definition msubst_efield_denote_nil_lemma: my_lemma.
reify_lemma reify_vst msubst_efield_denote_nil.
Defined.

(* Print msubst_efield_denote_nil_lemma. *)

Definition msubst_efield_denote_cons_struct_lemma (fld: ident) (efs: list efield) : my_lemma.
reify_lemma reify_vst (msubst_efield_denote_cons_struct fld efs).
Defined.

Definition msubst_efield_denote_cons_union_lemma (fld: ident) (efs: list efield) : my_lemma.
reify_lemma reify_vst (msubst_efield_denote_cons_union fld efs).
Defined.

Definition msubst_efield_denote_cons_array_lemma (ei: Clight.expr) (efs: list efield) : my_lemma.
reify_lemma reify_vst (msubst_efield_denote_cons_array ei efs).
Defined.

(* Print msubst_efield_denote_cons_array_lemma. *)

Section tbled.

Variable tbl : SymEnv.functions RType_typ.
Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Fixpoint solve_efield_denote (efs: list efield) : rtac typ (expr typ func) :=
  match efs with
  | nil => EAPPLY typ func msubst_efield_denote_nil_lemma
  | eStructField fld :: efs0 =>
      THEN (EAPPLY typ func (msubst_efield_denote_cons_struct_lemma fld efs0))
        (solve_efield_denote efs0)
  | eUnionField fld :: efs0 =>
      THEN (EAPPLY typ func (msubst_efield_denote_cons_union_lemma fld efs0))
        (solve_efield_denote efs0)
  | eArraySubsc ei :: efs0 =>
      THEN (THEN (EAPPLY typ func (msubst_efield_denote_cons_array_lemma ei efs0))
        (TRY (REFLEXIVITY_MSUBST tbl)))
        (solve_efield_denote efs0)
  end.


Check data_at.
Check Vfloat.
SearchAbout float.