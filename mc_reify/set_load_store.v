Require Import floyd.proofauto. 
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Lemma semax_set_localD:
  forall {Espec: OracleKind},
    forall temp var ret gt gs (* Delta *)
      id P T1 T2 R Post (e: Clight.expr) ty v,
      match PTree.get id temp with | Some (ty0, _) => Some ty0 | None => None end = Some ty ->
      is_neutral_cast (implicit_deref (typeof e)) ty = true ->
      msubst_eval_expr T1 T2 e = Some v ->
      tc_expr_b_norho (mk_tycontext temp var ret gt gs) e = true ->
      assertD P (localD (PTree.set id v T1) T2) R = Post ->
      semax (mk_tycontext temp var ret gt gs) (|> (assertD P (localD T1 T2) R))
        (Sset id e)
          (normal_ret_assert Post).
Proof.
  intros.
  subst Post.
  eapply semax_PTree_set; eauto.
  intro rho.
  apply tc_expr_b_sound with (rho := rho) in H2.
  normalize.
Qed.

Definition tc_LR_b_norho Delta e lr :=
  match lr with
  | LLLL => tc_lvalue_b_norho Delta e
  | RRRR => tc_expr_b_norho Delta e
  end.

Lemma semax_load_localD:
  forall {Espec: OracleKind},
    forall temp var ret gt gs (* Delta *)
      sh e n id P T1 T2 R Rn (e1: expr)
      (t t_root: type) (efs0 efs1: list efield) (gfs0 gfs1: list gfield) (tts0 tts1: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type2 t_root gfs0)) lr,
      match PTree.get id temp with | Some (ty0, _) => Some ty0 | None => None end = Some t ->
      is_neutral_cast (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) t = true ->
      length efs1 = length tts1 ->
      length gfs1 = length tts1 ->
      legal_nested_efield e t_root e1 (gfs1 ++ gfs0) (tts1 ++ tts0) lr = true ->
      nth_error R n = Some Rn ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_efield_denote T1 T2 (efs1 ++ efs0) = Some (gfs1 ++ gfs0) ->
      (local (tc_environ (mk_tycontext temp var ret gt gs))) && (assertD P (localD T1 T2) (Rn :: nil)) |--
        `(field_at sh t_root gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type2 t_root gfs0) gfs1 v') v ->
      tc_LR_b_norho (mk_tycontext temp var ret gt gs) e1 lr = true ->
      tc_efield_b_norho (mk_tycontext temp var ret gt gs) (efs1 ++ efs0) = true ->
      (local (tc_environ (mk_tycontext temp var ret gt gs))) && (assertD P (localD T1 T2) R) |--
        local `(tc_val (typeof (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0))) v) &&
        (!! legal_nested_field t_root (gfs1 ++ gfs0)) ->
      semax (mk_tycontext temp var ret gt gs) (|>assertD P (localD T1 T2) R) 
        (Sset id (nested_efield e1 (efs1 ++ efs0) (tts1 ++ tts0)))
          (normal_ret_assert
            (assertD P (localD (PTree.set id v T1) T2) R)).
Proof.
Abort.

(*
Require Import mc_reify.funcs.
Require Import mc_reify.types.
Require Import MirrorCore.Lambda.ExprCore.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.
*)