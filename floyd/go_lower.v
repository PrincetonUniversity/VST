Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_typecheck.
Require Import VST.floyd.semax_tactics.

Local Open Scope logic.

Ltac unfold_for_go_lower :=
  cbv delta [PROPx LOCALx SEPx locald_denote
                       eval_exprlist eval_expr eval_lvalue cast_expropt
                       sem_cast eval_binop eval_unop force_val1 force_val2
                      tc_expropt tc_expr tc_exprlist tc_lvalue tc_LR tc_LR_strong
                      msubst_tc_expropt msubst_tc_expr msubst_tc_exprlist msubst_tc_lvalue msubst_tc_LR (* msubst_tc_LR_strong *) msubst_tc_efield msubst_simpl_tc_assert 
                      typecheck_expr typecheck_exprlist typecheck_lvalue typecheck_LR typecheck_LR_strong typecheck_efield
                      function_body_ret_assert frame_ret_assert
                      make_args' bind_ret get_result1 retval
                       classify_cast
                       (* force_val sem_cast_neutral ... NOT THESE TWO!  *)
                      denote_tc_assert (* tc_andp tc_iszero *)
    liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry
     local lift lift0 lift1 lift2 lift3
   ] beta iota.

Lemma grab_tc_environ:
  forall Delta PQR S rho,
    (tc_environ Delta rho -> PQR rho |-- S) ->
    (local (tc_environ Delta) && PQR) rho |-- S.
Proof.
intros.
unfold PROPx,LOCALx in *; simpl in *.
normalize.
unfold local, lift1. normalize.
Qed.

Ltac go_lower0 :=
intros ?rho;
 try (simple apply grab_tc_environ; intro);
 repeat (progress unfold_for_go_lower; simpl).

Ltac old_go_lower :=
 go_lower0;
 autorewrite with go_lower;
 try findvars;
 simpl;
 autorewrite with go_lower;
 try match goal with H: tc_environ _ ?rho |- _ => clear H rho end.

Hint Rewrite eval_id_same : go_lower.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : go_lower.
(*Hint Rewrite Vint_inj' : go_lower.*)

(*** New go_lower stuff ****)

Lemma lower_one_temp:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some t ->
  (tc_val t v -> eval_id i rho = v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H0 by auto.
apply H0; auto.
apply tc_eval'_id_i with Delta; auto.
Qed.

Lemma lower_one_temp_Vint:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some t ->
  (tc_val t (Vint v) -> eval_id i rho = Vint v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i (Vint v) :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
eapply lower_one_temp; eauto.
Qed.

Lemma lower_one_lvar:
 forall t rho Delta P i v Q R S,
  (headptr v -> lvar_denote i t v rho ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (lvar i t v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H by auto.
apply H; auto.
hnf in H1.
destruct (Map.get (ve_of rho) i); try contradiction.
destruct p. destruct H1; subst.
hnf; eauto.
Qed.

Lemma finish_compute_le:  Lt = Gt -> False.
Proof. congruence. Qed.

Lemma lower_one_gvar:
 forall t rho Delta P i v Q R S,
  (glob_types Delta) ! i = Some t ->
  (headptr v -> gvar_denote i v rho ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (gvar i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H0 by auto.
apply H0; auto.
hnf in H2; destruct (Map.get (ve_of rho) i) as [[? ?] |  ]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst.
hnf; eauto.
Qed.

Lemma lower_one_sgvar:
 forall t rho Delta P i v Q R S,
  (glob_types Delta) ! i = Some t ->
  (headptr v -> sgvar_denote i v rho ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (sgvar i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H0 by auto.
apply H0; auto.
hnf in H2.
destruct (ge_of rho i); try contradiction.
subst.
hnf; eauto.
Qed.

Lemma lower_one_prop:
 forall  rho Delta P (P1: Prop) Q R S,
  (P1 ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (localprop P1 :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *.
normalize.
rewrite prop_true_andp in H by auto.
hnf in H1.
apply H; auto.
Qed.

Lemma lower_one_gvars:
 forall  rho Delta P gv Q R S,
  (gvars_denote gv rho ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (gvars gv :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *.
normalize.
rewrite prop_true_andp in H by auto.
hnf in H1.
apply H; auto.
Qed.

Lemma finish_lower:
  forall rho D R S,
  fold_right_sepcon R |-- S ->
  (local D && PROP() LOCAL() (SEPx R)) rho |-- S.
Proof.
intros.
simpl.
apply andp_left2.
unfold_for_go_lower; simpl. normalize.
Qed.

Lemma lower_one_temp_Vint':
 forall sz sg rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some (Tint sz sg noattr) ->
  ((exists j, v = Vint j /\ tc_val (Tint sz sg noattr) (Vint j) /\ eval_id i rho = (Vint j)) ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
eapply lower_one_temp; eauto.
intros.
apply H0; auto.
generalize H1; intro.
hnf in H3. destruct v; try contradiction.
exists i0. split3; auto.
Qed.
 
Ltac lower_one_temp_Vint' :=
 match goal with
 | a : name ?i |- (local _ && PROPx _ (LOCALx (temp ?i ?v :: _) _)) _ |-- _ =>
     simple eapply lower_one_temp_Vint';
     [ reflexivity | ];
     let tc := fresh "TC" in
     clear a; intros [a [? [tc ?EVAL]]]; unfold tc_val in tc; try subst v;
     revert tc; fancy_intro true
 | |- (local _ && PROPx _ (LOCALx (temp _ ?v :: _) _)) _ |-- _ =>
    is_var v;
     simple eapply lower_one_temp_Vint';
     [ reflexivity | ];
    let v' := fresh "v" in rename v into v';
     let tc := fresh "TC" in
     intros [v [? [tc ?EVAL]]]; unfold tc_val in tc; subst v';
     revert tc; fancy_intro true
 end.

Lemma lower_one_temp_trivial:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some t ->
  (tc_val t v ->
   (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R))) rho |-- S) ->
  (local (tc_environ Delta) && PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho |-- S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold local,lift1 in *.
simpl in *. unfold_lift.
normalize.
rewrite prop_true_andp in H0 by auto.
apply H0; auto.
apply tc_eval'_id_i with Delta; auto.
Qed.

Lemma quick_finish_lower:
  forall LHS,
  emp |-- !! True ->
  LHS |-- !! True.
Proof.
intros.
apply prop_right; auto.
Qed.

Definition localdef_tc (Delta: tycontext) (x: localdef): list Prop :=
  match x with
  | temp i v =>
      match (temp_types Delta) ! i with
      | Some t => tc_val t v :: nil
      | _ => nil
      end
  | lvar _ _ v =>
      isptr v :: headptr v :: nil
  | gvar i v
  | sgvar i v =>
      isptr v :: headptr v :: nil
  | _ => nil
  end.

Ltac pos_eqb_tac :=
  let H := fresh "H" in
  match goal with
  | |- context [Pos.eqb ?i ?j] => destruct (Pos.eqb i j) eqn:H; [apply Pos.eqb_eq in H | apply Pos.eqb_neq in H]
  end.

Lemma localdef_local_facts: forall Delta x,
  local (tc_environ Delta) && local (locald_denote x) |-- !! fold_right and True (localdef_tc Delta x).
Proof.
  intros.
  unfold local, lift1; unfold_lift.
  intros rho; simpl.
  rewrite <- prop_and.
  apply prop_derives.
  intros [? ?].
  destruct x; simpl in H0; unfold_lift in H0.
  + subst; simpl.
    destruct ((temp_types Delta) ! i) eqn:?; simpl; auto.
    destruct H0; subst.
    split; auto.
    revert H1.
    eapply tc_eval'_id_i; eauto.
  + simpl.
    assert (headptr v); [| split; [| split]; auto; apply headptr_isptr; auto].
    unfold lvar_denote in H0.
    destruct (Map.get (ve_of rho) i); [| inversion H0].
    destruct p, H0; subst.
    hnf; eauto.
  + simpl.
    assert (headptr v); [| split; [| split]; auto; apply headptr_isptr; auto].
    unfold gvar_denote in H0.
    destruct (Map.get (ve_of rho) i) as [[? ?] |]; [inversion H0 |].
    destruct (ge_of rho i); [| inversion H0].
    subst.
    hnf; eauto.
  + simpl.
    assert (headptr v); [| split; [| split]; auto; apply headptr_isptr; auto].
    unfold sgvar_denote in H0.
    destruct (ge_of rho i); [| inversion H0].
    subst.
    hnf; eauto.
  + simpl.
    auto.
  + simpl.
    auto.
Qed.

Lemma go_lower_localdef_one_step_canon_left: forall Delta Ppre l Qpre Rpre post,
  local (tc_environ Delta) && PROPx (Ppre ++ localdef_tc Delta l) (LOCALx (l :: Qpre) (SEPx Rpre)) |-- post ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx (l :: Qpre) (SEPx Rpre)) |-- post.
Proof.
  intros.
  apply derives_trans with (local (tc_environ Delta) && PROPx (Ppre ++ localdef_tc Delta l) (LOCALx (l :: Qpre) (SEPx Rpre))); auto.
  replace (PROPx (Ppre ++ localdef_tc Delta l)) with (PROPx (localdef_tc Delta l ++ Ppre)).
  Focus 2. {
    apply PROPx_Permutation.
    apply Permutation_app_comm.
  } Unfocus.
  rewrite <- !insert_local'.
  apply andp_right; [solve_andp |].
  apply andp_right; [solve_andp |].
  unfold PROPx. apply andp_right; [| solve_andp].
  rewrite <- andp_assoc.
  eapply derives_trans; [apply andp_derives; [apply localdef_local_facts | apply derives_refl] |].
  rewrite <- andp_assoc.
  apply andp_left1.
  remember (localdef_tc Delta l); clear.
  induction l0.
  + simpl fold_right.
    apply andp_left2; auto.
  + simpl fold_right.
    rewrite !prop_and, !andp_assoc.
    apply andp_derives; auto.
Qed.

Definition localdefs_tc (Delta: tycontext) (Pre: list localdef): list Prop :=
  concat (map (localdef_tc Delta) Pre).

Lemma go_lower_localdef_canon_left: forall Delta Ppre Qpre Rpre post,
  local (tc_environ Delta) && PROPx (Ppre ++ localdefs_tc Delta Qpre) (LOCALx nil (SEPx Rpre)) |-- post ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) |-- post.
Proof.
  intros.
  revert Ppre post H; induction Qpre; intros.
  + cbv [localdefs_tc concat rev map] in H.
    rewrite !app_nil_r in H; auto.
  + apply go_lower_localdef_one_step_canon_left.
    rewrite <- insert_local, (andp_comm _ (PROPx _ _)), <- andp_assoc, -> imp_andp_adjoint.
    apply IHQpre.
    rewrite <- imp_andp_adjoint.
    apply andp_left1.
    rewrite <- !app_assoc.
    eapply derives_trans; [exact H | auto].
Qed.

Definition msubst_extract_local (T1: PTree.t val) (T2: PTree.t vardesc) (x: localdef): Prop :=
  match x with
  | temp i u =>
    match T1 ! i with
    | Some v => v = u
    | None => False
    end
  | lvar i ti u =>
    match T2 ! i with
    | Some (vardesc_local_global tj v _)
    | Some (vardesc_local tj v) =>
      if eqb_type ti tj
      then v = u
      else False           
    | _ => False
    end
  | gvar i u =>
    match T2 ! i with
    | Some (vardesc_visible_global v) => v = u
    | _ => False
    end
  | sgvar i u =>
    match T2 ! i with
    | Some (vardesc_local_global _ _ v)
    | Some (vardesc_visible_global v)
    | Some (vardesc_shadowed_global v) => v = u
    | _ => False
    end
  | gvars gx =>
    
  | localprop P => P
  end.

Definition msubst_extract_locals (T1: PTree.t val) (T2: PTree.t vardesc) := map (msubst_extract_local T1 T2).

Lemma localdef_local_facts_inv: forall Delta P T1 T2 R x,
  msubst_extract_local T1 T2 x ->
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 nil) (SEPx R)) |-- local (locald_denote x).
Proof.
  intros.
  destruct x; simpl in H.
  + apply in_local.
    apply LocalD_sound_temp.
    destruct (T1 ! i); inv H; auto.
  + apply in_local.
    destruct (T2 ! i) as [[? | ? | ? | ?] |] eqn:?H; try solve [inv H].
    - destruct (eqb_type t t0) eqn:?H; [| inv H].
      apply eqb_type_spec in H1; subst.
      eapply LocalD_sound_local_global in H0.
      exact (proj1 H0).
    - destruct (eqb_type t t0) eqn:?H; [| inv H].
      apply eqb_type_spec in H1; subst.
      eapply LocalD_sound_local in H0.
      exact H0.
  + apply in_local.
    destruct (T2 ! i) as [[? | ? | ? | ?] |] eqn:?H; inv H.
    apply LocalD_sound_visible_global; auto.
  + destruct (T2 ! i) as [[? | ? | ? | ?] |] eqn:?H; inv H.
    - apply in_local.
      eapply LocalD_sound_local_global in H0.
      exact (proj2 H0).
    - eapply derives_trans; [| apply sgvar_gvar].
      apply in_local.
      apply LocalD_sound_visible_global; auto.
    - apply in_local.
      apply LocalD_sound_shadowed_global; auto.
  + unfold local, lift1; unfold_lift; intros ?.
    apply prop_right; auto.
Qed.

Lemma go_lower_localdef_one_step_canon_canon {cs: compspecs} : forall Delta Ppre Qpre Rpre Ppost l Qpost Rpost T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && PROPx (Ppost ++ msubst_extract_local T1 T2 l :: nil) (LOCALx Qpost (SEPx Rpost)) |-- PROPx Ppost (LOCALx (l :: Qpost) (SEPx Rpost)).
Proof.
  intros.
  replace (PROPx (Ppost ++ msubst_extract_local T1 T2 l :: nil)) with (PROPx (msubst_extract_local T1 T2 l :: Ppost)).
  Focus 2. {
    apply PROPx_Permutation.
    eapply Permutation_trans; [| apply Permutation_app_comm].
    apply Permutation_refl.
  } Unfocus.
  rewrite <- !insert_local', <- !insert_prop.
  apply andp_right; [| solve_andp].
  normalize.
  apply andp_left1.
  apply (local2ptree_soundness Ppre _ Rpre) in H; simpl in H.
  rewrite H.
  apply localdef_local_facts_inv; auto.
Qed.

Lemma go_lower_localdef_canon_canon {cs: compspecs} : forall Delta Ppre Qpre Rpre Ppost Qpost Rpost T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && PROPx (Ppost ++ msubst_extract_locals T1 T2 Qpost) (LOCALx nil (SEPx Rpost)) |-- PROPx Ppost (LOCALx Qpost (SEPx Rpost)).
Proof.
  intros.
  revert Ppost; induction Qpost; intros.
  + simpl app.
    rewrite app_nil_r.
    solve_andp.
  + eapply derives_trans; [| apply (go_lower_localdef_one_step_canon_canon Delta Ppre Qpre Rpre); eassumption].
    apply andp_right; [solve_andp |].
    eapply derives_trans; [| apply IHQpost].
    rewrite <- app_assoc; auto.
Qed.

Lemma go_lower_localdef_canon_tc_expr {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_expr Delta T1 T2 e) |-- tc_expr Delta e.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_expr_sound.
Qed.

Lemma go_lower_localdef_canon_tc_lvalue {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_lvalue Delta T1 T2 e) |-- tc_lvalue Delta e.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_lvalue_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_LR {cs: compspecs} : forall Delta Ppre Qpre Rpre e lr T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_LR Delta T1 T2 e lr) |-- tc_LR Delta e lr.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_LR_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_efield {cs: compspecs} : forall Delta Ppre Qpre Rpre efs T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_efield Delta T1 T2 efs) |-- tc_efield Delta efs.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_efield_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_exprlist {cs: compspecs} : forall Delta Ppre Qpre Rpre ts es T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_exprlist Delta T1 T2 ts es) |-- tc_exprlist Delta ts es.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_exprlist_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_expropt {cs: compspecs} : forall Delta Ppre Qpre Rpre e t T1 T2,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_expropt Delta T1 T2 e t) |-- tc_expropt Delta e t.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_expropt_sound; auto.
Qed.

Lemma go_lower_localdef_canon_eval_lvalue {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 u v,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  msubst_eval_lvalue T1 T2 e = Some u ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(!! (u = v)) |-- local (`(eq v) (eval_lvalue e)).
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  normalize.
  apply andp_left2, msubst_eval_lvalue_eq, H0.
Qed.

Lemma go_lower_localdef_canon_eval_expr {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 u v,
  local2ptree Qpre = (T1, T2, nil, nil) ->
  msubst_eval_expr T1 T2 e = Some u ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(!! (u = v)) |-- local (`(eq v) (eval_expr e)).
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  normalize.
  apply andp_left2, msubst_eval_expr_eq, H0.
Qed.

Inductive clean_LOCAL_right {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t vardesc): (environ -> mpred) -> mpred -> Prop :=
| clean_LOCAL_right_local_lift: forall P, clean_LOCAL_right Delta T1 T2 (local `P) (!! P)
| clean_LOCAL_right_prop: forall P, clean_LOCAL_right Delta T1 T2 (!! P) (!! P)
| clean_LOCAL_right_tc_lvalue: forall e, clean_LOCAL_right Delta T1 T2 (tc_lvalue Delta e) (msubst_tc_lvalue Delta T1 T2 e)
| clean_LOCAL_right_tc_expr: forall e, clean_LOCAL_right Delta T1 T2 (tc_expr Delta e) (msubst_tc_expr Delta T1 T2 e)
| clean_LOCAL_right_tc_LR: forall e lr, clean_LOCAL_right Delta T1 T2 (tc_LR Delta e lr) (msubst_tc_LR Delta T1 T2 e lr)
| clean_LOCAL_right_tc_efield: forall efs, clean_LOCAL_right Delta T1 T2 (tc_efield Delta efs) (msubst_tc_efield Delta T1 T2 efs)
| clean_LOCAL_right_tc_exprlist: forall ts es, clean_LOCAL_right Delta T1 T2 (tc_exprlist Delta ts es) (msubst_tc_exprlist Delta T1 T2 ts es)
| clean_LOCAL_right_tc_expropt: forall e t, clean_LOCAL_right Delta T1 T2 (tc_expropt Delta e t) (msubst_tc_expropt Delta T1 T2 e t)
| clean_LOCAL_right_canon: forall P Q R, clean_LOCAL_right Delta T1 T2 (PROPx P (LOCALx Q (SEPx R))) (!! (fold_right and True (P ++ msubst_extract_locals T1 T2 Q)) && fold_right_sepcon R)
| clean_LOCAL_right_eval_lvalue: forall e u v, msubst_eval_lvalue T1 T2 e = Some u -> clean_LOCAL_right Delta T1 T2 (local (`(eq v) (eval_lvalue e))) (!! (u = v))
| clean_LOCAL_right_eval_expr: forall e u v, msubst_eval_expr T1 T2 e = Some u -> clean_LOCAL_right Delta T1 T2 (local (`(eq v) (eval_expr e))) (!! (u = v))
| clean_LOCAL_right_andp: forall P1 P2 Q1 Q2, clean_LOCAL_right Delta T1 T2 P1 Q1 -> clean_LOCAL_right Delta T1 T2 P2 Q2 -> clean_LOCAL_right Delta T1 T2 (P1 && P2) (Q1 && Q2)
| clean_LOCAL_right_EX': forall A (P: A -> environ -> mpred) (Q: A -> mpred), (forall a, clean_LOCAL_right Delta T1 T2 (P a) (Q a)) -> clean_LOCAL_right Delta T1 T2 (exp P) (exp Q).

Lemma clean_LOCAL_right_EX: forall {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t vardesc) A (P: A -> environ -> mpred) (Q: A -> mpred),
  (forall a, exists Q', clean_LOCAL_right Delta T1 T2 (P a) Q' /\ Q' = Q a) ->
  clean_LOCAL_right Delta T1 T2 (exp P) (exp Q).
Proof.
  intros.
  apply clean_LOCAL_right_EX'.
  intros; specialize (H a).
  destruct H as [? [? ?]].
  subst; auto.
Qed.

Lemma clean_LOCAL_right_spec: forall {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t vardesc) P Q R S S',
  local2ptree Q = (T1, T2, nil, nil) ->
  clean_LOCAL_right Delta T1 T2 S S' ->
  local (tc_environ Delta) && PROPx (P ++ localdefs_tc Delta Q) (LOCALx nil (SEPx R)) |-- ` S' ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- S.
Proof.
  intros.
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- `S')
    by (apply go_lower_localdef_canon_left; auto).
  rewrite (add_andp _ _ H2); clear H1 H2.
  induction H0.
  + apply andp_left2; auto.
  + apply andp_left2; auto.
  + eapply go_lower_localdef_canon_tc_lvalue; eauto.
  + eapply go_lower_localdef_canon_tc_expr; eauto.
  + eapply go_lower_localdef_canon_tc_LR; eauto.
  + eapply go_lower_localdef_canon_tc_efield; eauto.
  + eapply go_lower_localdef_canon_tc_exprlist; eauto.
  + eapply go_lower_localdef_canon_tc_expropt; eauto.
  + eapply derives_trans; [| eapply (go_lower_localdef_canon_canon Delta P Q R); eauto].
    apply andp_right; [apply andp_left1; auto |].
    go_lowerx.
    normalize.
    solve_andp.
  + eapply go_lower_localdef_canon_eval_lvalue; eauto.
  + eapply go_lower_localdef_canon_eval_expr; eauto.
  + apply andp_right.
    - eapply derives_trans; [| apply IHclean_LOCAL_right1].
      unfold_lift; intros rho; simpl.
      solve_andp.
    - eapply derives_trans; [| apply IHclean_LOCAL_right2].
      unfold_lift; intros rho; simpl.
      solve_andp.
  + normalize.
    apply (exp_right x).
    apply H1.
Qed.

Ltac unfold_localdef_name QQ Q :=
  match Q with
  | nil => idtac
  | cons ?Qh ?Qt =>
    match Qh with
    | temp ?n _ => unfold n in QQ
    | lvar ?n _ _ => unfold n in QQ
    | gvar ?n _ => unfold n in QQ
    | sgvar ?n _ => unfold n in QQ
    end;
    unfold_localdef_name QQ Qt
  end.

Ltac solve_clean_LOCAL_right :=
  solve
    [ simple apply clean_LOCAL_right_local_lift
    | simple apply clean_LOCAL_right_prop
    | simple apply clean_LOCAL_right_tc_lvalue
    | simple apply clean_LOCAL_right_tc_expr
    | simple apply clean_LOCAL_right_tc_LR
    | simple apply clean_LOCAL_right_tc_efield
    | simple apply clean_LOCAL_right_tc_exprlist
    | simple apply clean_LOCAL_right_tc_expropt
    | simple apply clean_LOCAL_right_canon
    | simple apply clean_LOCAL_right_eval_lvalue; solve_msubst_eval_lvalue
    | simple apply clean_LOCAL_right_eval_expr; solve_msubst_eval_expr
    | simple apply clean_LOCAL_right_andp; solve_clean_LOCAL_right
    | simple apply clean_LOCAL_right_EX;
      let a := fresh "a" in
      intro a;
      eexists;
      split;
      [ solve_clean_LOCAL_right
      | match goal with
        | |- ?t = _ => super_pattern t a; reflexivity
        end
      ]
    ].

Ltac clean_LOCAL_canon_mix :=
  eapply clean_LOCAL_right_spec; [prove_local2ptree | solve_clean_LOCAL_right |];
         (let tl := fresh "tl" in
         let QQ := fresh "Q" in
         let PPr := fresh "Pr" in
         match goal with
         | |- context [?Pr ++ localdefs_tc ?Delta ?Q] =>
                set (tl := Pr ++ localdefs_tc Delta Q);
                set (PPr := Pr) in tl;
                set (QQ := Q) in tl;
                unfold Delta, abbreviate in tl;
                cbv [localdefs_tc localdef_tc temp_types tc_val concat map app Pos.eqb PTree.get] in tl;
                unfold_localdef_name QQ Q;
                subst PPr QQ;
                cbv beta iota zeta in tl;
                subst tl
         end).

Ltac go_lower :=
clear_Delta_specs;
intros;
match goal with
 | |- ENTAIL ?D, normal_ret_assert _ _ _ |-- _ =>
       apply ENTAIL_normal_ret_assert; fancy_intros true
 | |- local _ && _ |-- _ => idtac
 | |- ENTAIL _, _ |-- _ => idtac
 | _ => fail 10 "go_lower requires a proof goal in the form of (ENTAIL _ , _ |-- _)"
end;
clean_LOCAL_canon_mix;
repeat (simple apply derives_extract_PROP; fancy_intro true);
let rho := fresh "rho" in
intro rho;
first
[ simple apply quick_finish_lower
|          
 (simple apply finish_lower ||
 match goal with
 | |- (_ && PROPx nil _) _ |-- _ => fail 1 "LOCAL part of precondition is not a concrete list (or maybe Delta is not concrete)"
 | |- _ => fail 1 "PROP part of precondition is not a concrete list"
 end);
unfold_for_go_lower;
simpl; rewrite ?sepcon_emp;
clear_Delta;
try clear dependent rho].
