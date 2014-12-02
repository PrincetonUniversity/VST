Require Import floyd.proofauto. 
Require Import mc_reify.bool_funcs.
Local Open Scope logic.

Lemma semax_PTree_set:
  forall {Espec: OracleKind},
    forall Delta id P T1 T2 R (e2: Clight.expr) t v,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (implicit_deref (typeof e2)) t = true ->
      msubst_eval_expr T1 T2 e2 = Some v ->
      (local (tc_environ Delta)) && (assertD P (localD T1 T2) R) |--
        local (tc_expr Delta e2) ->
      semax Delta (|> (assertD P (localD T1 T2) R))
        (Sset id e2)
          (normal_ret_assert
            (assertD P (localD (PTree.set id v T1) T2) R)).
Proof.
  intros.
  unfold assertD, localD in *.
  rewrite insert_local in H2.
  eapply semax_post'.
  Focus 2. {
    eapply semax_SC_set; eauto.
    instantiate (1 := v).
    rewrite <- insert_local.
    apply andp_left2.
    apply msubst_eval_expr_eq, H1.
  } Unfocus.
  normalize.
  apply SC_remove_subst.
Qed.
