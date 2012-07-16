Require Import veric.base.
Require Import veric.expr.
Require Import veric.seplog.
Require Import msl.normalize.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import veric.SequentialClight.
Require Import msl.msl_standard.
Import SeqC CSL.

Lemma semax_post:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (forall ek vl rho, R' ek vl rho |-- R ek vl rho) ->
   semax Delta G P c R' ->  semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; eauto.
Qed.

Lemma semax_pre:
 forall P' Delta G P c R,
   (forall rho, typecheck_environ rho Delta = true ->  P  rho |-- P' rho) ->   semax Delta G P' c R  -> semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; eauto.
Qed.

Lemma env_gss:
  forall rho id v t, eval_expr (env_set rho id v) (Etempvar id t) = v.
Proof.
intros.  unfold eval_expr, env_set; simpl. rewrite PTree.gss. simpl. auto.
Qed.

Lemma env_gso:
  forall rho id id' v t, id <> id' -> 
      eval_expr (env_set rho id' v) (Etempvar id t) = eval_expr rho (Etempvar id t).
Proof.
intros.  unfold eval_expr, env_set; simpl.
rewrite PTree.gso by auto. auto.
Qed.

Definition force_int (v: val) := 
 match v with
 | Vint i => i | _ => Int.zero 
 end.

Lemma extract_exists_pre:
      forall
        (A : Type) (any: A) (P : A -> assert) (c : Clight.statement)
         Delta (G : funspecs) (R : ret_assert),
       (forall x : A, semax Delta G (P x) c R) ->
       semax Delta G (fun rho => exp (fun x => P x rho)) c R.
Proof.
intros.
apply semax_post with (existential_ret_assert (fun _:A => R)).
intros ek vl rho w ?.
simpl in H0. destruct H0; auto.
apply extract_exists; auto.
Qed.
