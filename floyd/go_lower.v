Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_typecheck.
Require Import VST.floyd.semax_tactics.
Import LiftNotation.
Import -(notations) compcert.lib.Maps.

Ltac unfold_for_go_lower :=
  cbv delta [PROPx LAMBDAx PARAMSx GLOBALSx LOCALx SEPx argsassert2assert locald_denote
                       eval_exprlist eval_expr eval_lvalue cast_expropt
                       eval_binop eval_unop force_val1 force_val2
                      msubst_tc_expropt msubst_tc_expr msubst_tc_exprlist msubst_tc_lvalue msubst_tc_LR (* msubst_tc_LR_strong *) msubst_tc_efield msubst_simpl_tc_assert 
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
  forall `{!VSTGS OK_ty Σ} Delta (PQR : assert) S rho,
    (tc_environ Delta rho -> PQR rho ⊢ S) ->
    (local(Σ := Σ) (tc_environ Delta) ∧ PQR) rho ⊢ S.
Proof.
intros.
unfold PROPx,LOCALx in *; simpl in *.
monPred.unseal.
by apply bi.pure_elim_l.
Qed.

Ltac go_lower0 :=
try monPred.unseal; constructor;
intros ?rho;
 try (simple apply grab_tc_environ; intro);
 repeat (progress unfold_for_go_lower; simpl).

#[export] Hint Rewrite eval_id_same : go_lower.
#[export] Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : go_lower.
(*#[export] Hint Rewrite Vint_inj' : go_lower.*)

(*** New go_lower stuff ****)

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Local Notation LOCALx := (LOCALx(Σ := Σ)).

Lemma lower_one_temp:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) !! i = Some t ->
  (tc_val t v -> eval_id i rho = v ->
   (local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R))) rho ⊢ S) ->
  (local (tc_environ Delta) ∧ PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho ⊢ S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
revert H0; monPred.unseal; intros H0.
unfold_lift; apply bi.pure_elim_l; intros.
apply bi.pure_elim_l; intros (-> & ?).
rewrite -H0 //.
- normalize.
- apply tc_val_tc_val'; last done.
  apply tc_eval'_id_i with Delta; auto.
Qed.

Lemma lower_one_temp_Vint:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) !! i = Some t ->
  (tc_val t (Vint v) -> eval_id i rho = Vint v ->
   (local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R))) rho ⊢ S) ->
  (local (tc_environ Delta) ∧ PROPx P (LOCALx (temp i (Vint v) :: Q) (SEPx R))) rho ⊢ S.
Proof.
intros.
eapply lower_one_temp; eauto.
Qed.

Lemma lower_one_lvar:
 forall t rho Delta P i v Q R S,
  (headptr v -> lvar_denote i t v rho ->
   (local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R))) rho ⊢ S) ->
  (local (tc_environ Delta) ∧ PROPx P (LOCALx (lvar i t v :: Q) (SEPx R))) rho ⊢ S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
rewrite assoc (bi.and_comm (local _)) -assoc.
revert H; monPred.unseal; intros H.
apply bi.pure_elim_l; intros Hlvar.
apply H; auto.
unfold lvar_denote in Hlvar.
destruct (Map.get (ve_of rho) i) as [(?, ?)|]; try contradiction.
destruct Hlvar; unfold headptr; eauto.
Qed.

Lemma finish_compute_le:  Lt = Gt -> False.
Proof. congruence. Qed.

Lemma gvars_denote_HP: forall rho Delta gv i t,
  gvars_denote gv rho ->
  tc_environ Delta rho ->
  (glob_types Delta) !! i = Some t ->
  headptr (gv i).
Proof.
  intros.
  hnf in H. red in H0.
  subst.
  destruct_glob_types i.
  rewrite Heqo0.
  hnf; eauto.
Qed.

Lemma lower_one_gvars:
 forall  rho Delta P gv Q R S,
  ((forall i t, (glob_types Delta) !! i = Some t -> headptr (gv i)) -> gvars_denote gv rho ->
   (local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R))) rho ⊢ S) ->
  (local (tc_environ Delta) ∧ PROPx P (LOCALx (gvars gv :: Q) (SEPx R))) rho ⊢ S.
Proof.
  intros.
  rewrite <- insert_local.
  forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
  revert H; monPred.unseal; intros H.
  apply bi.pure_elim_l; intros.
  apply bi.pure_elim_l; intros.
  rewrite -H //; first normalize.
  intros.
  eapply gvars_denote_HP; eauto.
Qed.

Lemma finish_lower:
  forall rho (D: environ -> Prop) R S,
  (D rho -> fold_right_sepcon R ⊢ S) ->
  (local D ∧ PROP() LOCAL() (SEPx R) : @assert Σ)%assert rho ⊢ S.
Proof.
intros.
simpl.
unfold_for_go_lower; simpl; monPred.unseal.
normalize.
Qed.

Lemma lower_one_temp_Vint':
 forall sz sg rho Delta P i v Q R S,
  (temp_types Delta) !! i = Some (Tint sz sg noattr) ->
  ((exists j, v = Vint j /\ tc_val (Tint sz sg noattr) (Vint j) /\ eval_id i rho = (Vint j)) ->
   (local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R))) rho ⊢ S) ->
  (local (tc_environ Delta) ∧ PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho ⊢ S.
Proof.
intros.
eapply lower_one_temp; eauto.
intros.
apply H0; auto.
generalize H1; intro.
hnf in H3. destruct v; try contradiction.
exists i0. split3; auto.
Qed.

Lemma lower_one_temp_trivial:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) !! i = Some t ->
  (tc_val t v ->
   (local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R))) rho ⊢ S) ->
  (local (tc_environ Delta) ∧ PROPx P (LOCALx (temp i v :: Q) (SEPx R))) rho ⊢ S.
Proof.
intros.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
revert H0; monPred.unseal; intros H0.
unfold_lift; apply bi.pure_elim_l; intros.
apply bi.pure_elim_l; intros (-> & ?).
rewrite -H0 //; first normalize.
apply tc_val_tc_val'; last done.
apply tc_eval'_id_i with Delta; auto.
Qed.

Lemma quick_finish_lower:
  forall {B : bi} (LHS : B),
  (emp ⊢ ⌜True⌝ : B) ->
  LHS ⊢ ⌜True⌝.
Proof.
intros.
apply bi.True_intro.
Qed.

Fixpoint remove_localdef (x: localdef) (l: list localdef) : list localdef :=
  match l with
  | nil => nil
  | y :: l0 =>
     match x, y with
     | temp i u, temp j v =>
       if Pos.eqb i j
       then remove_localdef x l0
       else y :: remove_localdef x l0
     | lvar i ti u, lvar j tj v =>
       if Pos.eqb i j
       then remove_localdef x l0
       else y :: remove_localdef x l0
     | _, _ => y :: remove_localdef x l0
     end
  end.

Definition localdef_tc (Delta: tycontext) (gvar_idents: list ident) (x: localdef): list Prop :=
  match x with
  | temp i v =>
      match (temp_types Delta) !! i with
      | Some t => tc_val t v :: nil
      | _ => nil
      end
  | lvar _ _ v =>
      isptr v :: headptr v :: nil
  | gvars gv =>
      VST_floyd_map (fun id => headptr (gv id)) gvar_idents
  end.

Definition legal_glob_ident (Delta: tycontext) (i: ident): bool :=
  match (glob_types Delta) !! i with
  | Some _ => true
  | _ => false
  end.

Local Notation local := (local(Σ := Σ)).

Lemma localdef_local_facts: forall Delta gvar_ident x,
  fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true ->
  local (tc_environ Delta) ∧ local (locald_denote x) ⊢ ⌜fold_right and True (localdef_tc Delta gvar_ident x)⌝.
Proof.
  intros ??? LEGAL.
  monPred.unseal; split => rho; simpl.
  rewrite /lift1 -bi.pure_and.
  apply bi.pure_elim'; intros (? & ?).
  apply bi.pure_intro.
  destruct x; simpl in H0; unfold_lift in H0.
  + subst; simpl.
    destruct ((temp_types Delta) !! i) eqn:?; simpl; auto.
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
  + unfold localdef_tc.
    induction gvar_ident; [exact I |].
    simpl in LEGAL.
    rewrite andb_true_iff in LEGAL.
    destruct LEGAL as [LEGAL0 LEGAL].
    split; [clear IHgvar_ident | apply IHgvar_ident; auto].
    unfold gvars_denote in H0.
    subst g.
    unfold legal_glob_ident in LEGAL0.
    red in H.
    destruct_glob_types a.
      2: rewrite Heqo in LEGAL0; inv LEGAL0.
    rewrite Heqo0.
    hnf; eauto.
Qed.

Lemma fold_right_and_app' : forall P1 P2, foldr and True%type (P1 ++ P2) <-> foldr and True%type P1 /\ foldr and True%type P2.
Proof.
  intros; induction P1; simpl; tauto.
Qed.

Lemma go_lower_localdef_one_step_canon_left: forall Delta Ppre l Qpre Rpre post gvar_ident
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  (local (tc_environ Delta) ∧ PROPx (Ppre ++ localdef_tc Delta gvar_ident l) (LOCALx (l :: Qpre) (SEPx Rpre)) ⊢ post) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx (l :: Qpre) (SEPx Rpre)) ⊢ post.
Proof.
  intros.
  rewrite -H.
  rewrite (PROPx_Permutation (_ ++ _)); last by apply Permutation_app_comm.
  rewrite <- !insert_local'.
  apply bi.and_intro; [solve_andp |].
  apply bi.and_intro; [solve_andp |].
  unfold PROPx. apply bi.and_intro; [| rewrite /LOCALx; solve_andp].
  rewrite assoc localdef_local_facts //.
  rewrite fold_right_and_app'.
  normalize.
Qed.

Definition localdefs_tc (Delta: tycontext) gvar_ident (Pre: list localdef): list Prop :=
  VST_floyd_concat (VST_floyd_map (localdef_tc Delta gvar_ident) Pre).

Lemma go_lower_localdef_canon_left: forall Delta Ppre Qpre Rpre post gvar_ident
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  (local (tc_environ Delta) ∧ PROPx (Ppre ++ localdefs_tc Delta gvar_ident Qpre) (LOCALx nil (SEPx Rpre)) ⊢ post) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ⊢ post.
Proof.
  intros.
  revert Ppre post H; induction Qpre; intros.
  + cbv [localdefs_tc concat rev map ] in H.
    rewrite !app_nil_r in H; auto.
  + eapply go_lower_localdef_one_step_canon_left; eauto.
    rewrite -insert_local (bi.and_comm _ (PROPx _ _)) assoc.
    apply bi.impl_elim_l'.
    apply IHQpre.
    apply bi.impl_intro_l.
    rewrite bi.and_elim_r -app_assoc //.
Qed.

Inductive No_value_for_temp_variable (i: ident) : Prop := .
Inductive No_value_for_lvar_variable (i: ident) : Prop := .
Inductive Wrong_type_for_lvar_variable (i: ident) : Prop := .
Inductive Missing_gvars (gv: globals) : Prop := .

Definition msubst_extract_local (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) (x: localdef): Prop :=
  match x with
  | temp i u =>
    match T1 !! i with
    | Some v => u = v
    | None => No_value_for_temp_variable i
    end
  | lvar i ti u =>
    match T2 !! i with
    | Some (tj, v) =>
      if eqb_type ti tj
      then u = v
      else Wrong_type_for_lvar_variable i
    | _ => No_value_for_lvar_variable i
    end
  | gvars gv =>
    match GV with
    | Some gv0 => gv0 = gv
    | _ => Missing_gvars gv
    end
  end.

Definition msubst_extract_locals (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) := VST_floyd_map (msubst_extract_local Delta T1 T2 GV).

Lemma localdef_local_facts_inv: forall Delta P T1 T2 GV R x,
  msubst_extract_local Delta T1 T2 GV x ->
  local (tc_environ Delta) ∧ PROPx P (LOCALx (LocalD T1 T2 GV) (SEPx R)) ⊢ local (locald_denote x).
Proof.
  intros.
  destruct x; simpl in H.
  + apply in_local.
    apply LocalD_sound_temp.
    destruct (T1 !! i); inv H; auto.
  + apply in_local.
    destruct (T2 !! i) as [[? ?] |] eqn:?H; try solve [inv H].
    destruct (eqb_type t t0) eqn:?H; [| inv H].
    apply eqb_type_spec in H1; subst.
    eapply LocalD_sound_local in H0.
    exact H0.
  + apply in_local.
    destruct GV as [? |] eqn:?H; try solve [inv H].
    subst g0 GV.
    apply LocalD_sound_gvars; auto.
Qed.

Lemma go_lower_localdef_one_step_canon_canon: forall Delta Ppre Qpre Rpre Ppost l Qpost Rpost T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ PROPx (Ppost ++ msubst_extract_local Delta T1 T2 GV l :: nil) (LOCALx Qpost (SEPx Rpost)) ⊢ PROPx Ppost (LOCALx (l :: Qpost) (SEPx Rpost)).
Proof.
  intros.
  rewrite (PROPx_Permutation (_ ++ _)); last by apply Permutation_app_comm.
  rewrite /= -!insert_local' -!insert_prop.
  apply bi.and_intro; [| rewrite /PROPx /LOCALx; solve_andp].
  apply (local2ptree_soundness Ppre _ Rpre) in H; simpl in H.
  rewrite H.
  rewrite assoc comm -assoc; apply bi.pure_elim_l; intros.
  rewrite bi.and_elim_r.
  apply localdef_local_facts_inv; auto.
Qed.

Lemma go_lower_localdef_canon_canon : forall Delta Ppre Qpre Rpre Ppost Qpost Rpost T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ PROPx (Ppost ++ msubst_extract_locals Delta T1 T2 GV Qpost) (LOCALx nil (SEPx Rpost)) ⊢ PROPx Ppost (LOCALx Qpost (SEPx Rpost)).
Proof.
  intros.
  revert Ppost; induction Qpost; intros.
  + simpl app.
    rewrite app_nil_r.
    rewrite /PROPx /LOCALx; solve_andp.
  + rewrite -(go_lower_localdef_one_step_canon_canon _ Ppre _ Rpre); last done.
    apply bi.and_intro; [solve_andp |].
    apply bi.and_intro; [rewrite /PROPx /LOCALx; solve_andp|].
    rewrite -IHQpost -app_assoc //.
Qed.

Lemma go_lower_localdef_canon_tc_expr {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ assert_of `(msubst_tc_expr Delta T1 T2 GV e) ⊢ tc_expr Delta e.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_expr_sound.
Qed.

Lemma go_lower_localdef_canon_tc_lvalue {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ assert_of `(msubst_tc_lvalue Delta T1 T2 GV e) ⊢ tc_lvalue Delta e.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_lvalue_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_LR {cs: compspecs} : forall Delta Ppre Qpre Rpre e lr T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ assert_of `(msubst_tc_LR Delta T1 T2 GV e lr) ⊢ tc_LR Delta e lr.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_LR_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_efield {cs: compspecs} : forall Delta Ppre Qpre Rpre efs T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ assert_of `(msubst_tc_efield Delta T1 T2 GV efs) ⊢ tc_efield Delta efs.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_efield_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_exprlist {cs: compspecs} : forall Delta Ppre Qpre Rpre ts es T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ assert_of `(msubst_tc_exprlist Delta T1 T2 GV ts es) ⊢ tc_exprlist Delta ts es.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_exprlist_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_expropt {cs: compspecs} : forall Delta Ppre Qpre Rpre e t T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ assert_of `(msubst_tc_expropt Delta T1 T2 GV e t) ⊢ tc_expropt Delta e t.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_expropt_sound; auto.
Qed.

Lemma go_lower_localdef_canon_eval_lvalue {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV u v,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  msubst_eval_lvalue Delta T1 T2 GV e = Some u ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ local (`(u = v)) ⊢ local (`(eq v) (eval_lvalue e)).
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  rewrite assoc msubst_eval_lvalue_eq //.
  normalize.
  apply bi.pure_elim_r; intros ->; done.
Qed.

Lemma go_lower_localdef_canon_eval_expr {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV u v,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  msubst_eval_expr Delta T1 T2 GV e = Some u ->
  local (tc_environ Delta) ∧ PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ∧ local `(u = v) ⊢ local (`(eq v) (eval_expr e)).
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  rewrite assoc msubst_eval_expr_eq //.
  normalize.
  apply bi.pure_elim_r; intros ->; done.
Qed.

Inductive clean_LOCAL_right (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals): assert -> mpred -> Prop :=
| clean_LOCAL_right_sep_lift: forall P, clean_LOCAL_right Delta T1 T2 GV (assert_of (`P)) (P)
| clean_LOCAL_right_local_lift: forall P, clean_LOCAL_right Delta T1 T2 GV (local (`P)) (⌜P⌝)
| clean_LOCAL_right_prop: forall P, clean_LOCAL_right Delta T1 T2 GV (⌜P⌝) (⌜P⌝)
| clean_LOCAL_right_tc_lvalue: forall (cs: compspecs) e, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_lvalue Delta e)) (msubst_tc_lvalue Delta T1 T2 GV e)
| clean_LOCAL_right_tc_expr: forall (cs: compspecs) e, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_expr Delta e)) (msubst_tc_expr Delta T1 T2 GV e)
| clean_LOCAL_right_tc_LR: forall (cs: compspecs) e lr, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_LR Delta e lr)) (msubst_tc_LR Delta T1 T2 GV e lr)
| clean_LOCAL_right_tc_efield: forall (cs: compspecs) efs, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_efield Delta efs)) (msubst_tc_efield Delta T1 T2 GV efs)
| clean_LOCAL_right_tc_exprlist: forall (cs: compspecs)  ts es, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_exprlist Delta ts es)) (msubst_tc_exprlist Delta T1 T2 GV ts es)
| clean_LOCAL_right_tc_expropt: forall (cs: compspecs) e t, clean_LOCAL_right Delta T1 T2 GV (tc_expropt Delta e t) (msubst_tc_expropt Delta T1 T2 GV e t)
| clean_LOCAL_right_canon': forall P Q R, clean_LOCAL_right Delta T1 T2 GV (PROPx P (LOCALx Q (SEPx R))) (fold_right_PROP_SEP (P ++ msubst_extract_locals Delta T1 T2 GV Q) R)
| clean_LOCAL_right_eval_lvalue: forall  (cs: compspecs) e u v, msubst_eval_lvalue Delta T1 T2 GV e = Some u -> clean_LOCAL_right Delta T1 T2 GV (local (`(eq v) (eval_lvalue e))) (⌜u = v⌝)
| clean_LOCAL_right_eval_expr: forall  (cs: compspecs) e u v, msubst_eval_expr Delta T1 T2 GV e = Some u -> clean_LOCAL_right Delta T1 T2 GV (local (`(eq v) (eval_expr e))) (⌜u = v⌝)
| clean_LOCAL_right_andp: forall P1 P2 Q1 Q2, clean_LOCAL_right Delta T1 T2 GV P1 Q1 -> clean_LOCAL_right Delta T1 T2 GV P2 Q2 -> clean_LOCAL_right Delta T1 T2 GV (P1 ∧ P2) (Q1 ∧ Q2)
| clean_LOCAL_right_tc_andp: forall {cs : compspecs} P1 P2 Q1 Q2, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert P1) Q1 -> clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert P2) Q2 -> clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (tc_andp P1 P2)) (Q1 ∧ Q2)
| clean_LOCAL_right_EX': forall A (P: A -> assert) (Q: A -> mpred), (forall a, clean_LOCAL_right Delta T1 T2 GV (P a) (Q a)) -> clean_LOCAL_right Delta T1 T2 GV (∃ x, P x) (∃ x, Q x).

Lemma clean_LOCAL_right_True (Delta : tycontext) (T1 : PTree.t val) (T2 : PTree.t (type * val)) (GV : option globals): clean_LOCAL_right Delta T1 T2 GV True True.
Proof.
  exact (clean_LOCAL_right_prop _ _ _ _ True).
Qed.

Lemma clean_LOCAL_right_False (Delta : tycontext) (T1 : PTree.t val) (T2 : PTree.t (type * val)) (GV : option globals): clean_LOCAL_right Delta T1 T2 GV False False.
Proof.
  exact (clean_LOCAL_right_prop _ _ _ _ False).
Qed.

Lemma clean_LOCAL_right_canon (Delta : tycontext) (T1 : PTree.t val) (T2 : PTree.t (type * val)) (GV : option globals): forall P Q R Res, (fold_right_PROP_SEP (VST_floyd_app P (msubst_extract_locals Delta T1 T2 GV Q)) R) = Res -> clean_LOCAL_right Delta T1 T2 GV (PROPx P (LOCALx Q (SEPx R))) Res.
Proof.
  intros.
  subst Res.
  apply clean_LOCAL_right_canon'.
Qed.

(* clean_LOCAL_right is syntactic except for this lemma -- maybe we should just add it as a case?
Lemma clean_LOCAL_right_tc_andp {cs: compspecs} (Delta : tycontext) (T1 : PTree.t val) (T2 : PTree.t (type * val)) (GV : option globals): forall P1 P2 Q1 Q2, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert P1) Q1 -> clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert P2) Q2 -> clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (tc_andp P1 P2)) (Q1 ∧ Q2).
Proof.
  intros.
  simpl.
  rewrite denote_tc_assert_andp.
  apply clean_LOCAL_right_andp; auto.
Qed.*)

Lemma clean_LOCAL_right_EX: forall (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) A (P: A -> assert) (Q: A -> mpred),
  (forall a, exists Q', clean_LOCAL_right Delta T1 T2 GV (P a) Q' /\ Q' = Q a) ->
  clean_LOCAL_right Delta T1 T2 GV (∃ x, P x) (∃ x, Q x).
Proof.
  intros.
  apply clean_LOCAL_right_EX'.
  intros; specialize (H a).
  destruct H as [? [? ?]].
  subst; auto.
Qed.

Lemma clean_LOCAL_right_aux: forall gvar_ident (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R)) ∧ assert_of (` S') ⊢ S.
Proof.
  intros.
  induction H0.
  + solve_andp.
  + solve_andp.
  + rewrite lift0C_prop; solve_andp.
  + eapply go_lower_localdef_canon_tc_lvalue; eauto.
  + eapply go_lower_localdef_canon_tc_expr; eauto.
  + eapply go_lower_localdef_canon_tc_LR; eauto.
  + eapply go_lower_localdef_canon_tc_efield; eauto.
  + eapply go_lower_localdef_canon_tc_exprlist; eauto.
  + eapply go_lower_localdef_canon_tc_expropt; eauto.
  + etrans; [| eapply (go_lower_localdef_canon_canon Delta P Q R); eauto].
    apply bi.and_intro; [rewrite bi.and_elim_l; auto |].
    go_lowerx.
    rewrite fold_right_PROP_SEP_spec.
    normalize.
  + eapply go_lower_localdef_canon_eval_lvalue; eauto.
  + eapply go_lower_localdef_canon_eval_expr; eauto.
  + rewrite lift0C_andp; apply bi.and_intro.
    - rewrite -IHclean_LOCAL_right1.
      rewrite /PROPx /LOCALx; solve_andp.
    - rewrite -IHclean_LOCAL_right2.
      rewrite /PROPx /LOCALx; solve_andp.
  + rewrite lift0C_andp denote_tc_assert_andp; apply bi.and_intro.
    - rewrite -IHclean_LOCAL_right1.
      rewrite /PROPx /LOCALx; solve_andp.
    - rewrite -IHclean_LOCAL_right2.
      rewrite /PROPx /LOCALx; solve_andp.
  + rewrite lift0C_exp !bi.and_exist_l; apply bi.exist_elim; intros.
    rewrite -bi.exist_intro //.
Qed.

Lemma clean_LOCAL_right_spec: forall gvar_ident (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  (local (tc_environ Delta) ∧ PROPx (VST_floyd_app P (localdefs_tc Delta gvar_ident Q)) (LOCALx nil (SEPx R)) ⊢ assert_of (` S')) ->
  local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R)) ⊢ S.
Proof.
  intros.
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ assert_of (`S'))
    by (eapply go_lower_localdef_canon_left; eauto).
  rewrite (add_andp _ _ H2); clear H1 H2.
  rewrite -assoc; eapply clean_LOCAL_right_aux; eauto.
Qed.

(* This version of clean_LOCAL_right (with "bangbang") is to
 support then entailer!! tactic [notation] that avoids putting above 
 the line all the type-checking consequences of the LOCAL defs. *)
Lemma clean_LOCAL_right_spec_bangbang: forall gvar_ident
   (Delta: tycontext) (T1: Maps.PTree.t val) (T2: Maps.PTree.t (Ctypes.type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  (local (tc_environ Delta) ∧ PROPx P (LOCALx nil (SEPx R)) ⊢ assert_of (liftx S')) ->
  local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R)) ⊢ S.
Proof.
  intros.
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ assert_of (`S')). {
    eapply go_lower_localdef_canon_left; try eassumption.
    eapply ENTAIL_trans; try eassumption.
    rewrite bi.and_elim_r.
    clear.
    apply bi.and_mono; last done.
    rewrite fold_right_and_app' bi.pure_and bi.and_elim_l //.
  }
  rewrite (add_andp _ _ H2); clear H1 H2.
  rewrite -assoc; eapply clean_LOCAL_right_aux; eauto.
Qed.

Lemma clean_LOCAL_right_bupd_spec: forall gvar_ident (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  (local (tc_environ Delta) ∧ PROPx (VST_floyd_app P (localdefs_tc Delta gvar_ident Q)) (LOCALx nil (SEPx R)) ⊢ (|==> assert_of (` S'))) ->
  local (tc_environ Delta) ∧ PROPx P (LOCALx Q (SEPx R)) ⊢ |==> S.
Proof.
  intros.
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ |==> assert_of (`S'))
    by (eapply go_lower_localdef_canon_left; eauto).
  pose proof clean_LOCAL_right_aux _ _ _ _ _ P _ (True :: nil) _ _ LEGAL H H0.
  rewrite (add_andp _ _ H2); clear H1 H2.
  rewrite -H3.
  etrans.
  + apply bi.and_mono; last done.
    apply bi.and_mono; first done.
    instantiate (1 := PROPx P (LOCALx Q (SEPx (True::nil)))).
    rewrite /PROPx /LOCALx /SEPx /= bi.sep_emp.
    repeat (apply bi.and_mono; first done).
    rewrite embed_pure; apply bi.True_intro.
  + rewrite /PROPx /LOCALx /SEPx /local /lift1; monPred.unseal; split => rho; simpl.
    iIntros "(#(? & ? & ? & ?) & >$) !>"; auto.
Qed.

End mpred.

Ltac check_safe_subst z :=
 try (repeat lazymatch goal with
       | H: z = ?A |- _ => match A with context [z] => revert H end
       | H: ?A = z |- _ => match A with context [z] => revert H end
       | H: ?A |- _ => match A with context [z] => revert H end
       end;
    match goal with |- ?G => 
       try (has_evar G; fail 3 "subst not performed because the goal contains evars") 
    end;
   fail).

Ltac safe_subst z :=
  check_safe_subst z; subst z.

Ltac safe_subst_any :=
  repeat
   match goal with
   | H:?x = ?y |- _ => first [ safe_subst x | safe_subst y ]
   end.

(* safe_subst is meant to avoid doing rewrites or substitution of variables that
  are in the scope of a unification variable.  See issue #186. *)

Ltac lower_one_temp_Vint' :=
 match goal with
 | |- (local _ ∧ PROPx _ (LOCALx (temp _ ?v :: _) _)) _ ⊢ _ =>
    is_var v;
     simple eapply lower_one_temp_Vint';
     [ reflexivity | ];
    let v' := fresh "v" in rename v into v';
     let tc := fresh "TC" in
     intros [v [? [tc ?EVAL]]]; unfold tc_val in tc; safe_subst v';
     revert tc; fancy_intro true
 end.

Ltac gvar_headptr_intro_case1 gv H i :=
         match goal with
         | _ := gv i |- _ => fail 1
         | H: isptr (gv i), H': headptr (gv i) |- _ => fail 1
         | _ => generalize (H i _ ltac:(first[reflexivity | eassumption])); fancy_intro true
         end.

Ltac gvar_headptr_intro_case2 gv H x i :=
         match goal with
         | H: isptr x, H': headptr x |- _ => fail 1
         | _ => generalize ((H i _ ltac:(first[reflexivity | eassumption])): headptr x); fancy_intro true
         end.

Ltac gvar_headptr_intro gv H:=
  repeat
     match goal with
     | x:= gv ?i |- _ =>
         gvar_headptr_intro_case2 gv H x i
     | |- context [gv ?i] =>
         gvar_headptr_intro_case1 gv H i
     | _: context [gv ?i] |- _ =>
         gvar_headptr_intro_case1 gv H i
     | x:= context [gv ?i] |- _ =>
         gvar_headptr_intro_case1 gv H i
     end.

Ltac unfold_localdef_name QQ Q :=
  match Q with
  | nil => idtac
  | cons ?Qh ?Qt =>
    match Qh with
    | temp ?n _ => unfold n in QQ
    | lvar ?n _ _ => unfold n in QQ
    | _ => idtac
    end;
    unfold_localdef_name QQ Qt
  end.

Ltac unify_for_go_lower :=
    match goal with |- fold_right_PROP_SEP (VST_floyd_app ?A ?B) ?C = _ =>
      repeat match B with context [(?x = ?y) :: _] =>
       has_evar x; progress (unify x y)
      end
    end.

Ltac simply_msubst_extract_locals :=
  unfold msubst_extract_locals, msubst_extract_local, VST_floyd_map;
  cbv iota zeta beta;
  simpl_PTree_get; 
  try prove_eqb_type
 (* ; simpl_eqb_type *).

Ltac solve_clean_LOCAL_right :=
  solve
    [ simple apply clean_LOCAL_right_sep_lift
    | simple apply clean_LOCAL_right_local_lift
    | simple apply clean_LOCAL_right_prop
    | simple apply clean_LOCAL_right_True
    | simple apply clean_LOCAL_right_False
    | try unfold tc_lvalue; simple apply clean_LOCAL_right_tc_lvalue
    | try unfold tc_expr; simple apply clean_LOCAL_right_tc_expr
    | try unfold tc_LR; simple apply clean_LOCAL_right_tc_LR
    | try unfold tc_efield; simple apply clean_LOCAL_right_tc_efield
    | try unfold tc_exprlist; simple apply clean_LOCAL_right_tc_exprlist
    | simple apply clean_LOCAL_right_tc_expropt
    | simple apply clean_LOCAL_right_canon;
      simply_msubst_extract_locals;
      unify_for_go_lower;
      unfold VST_floyd_app;
      unfold fold_right_PROP_SEP, fold_right_and_True;
      cbv [fold_right_sepcon];
      reflexivity
    | simple apply clean_LOCAL_right_eval_lvalue; solve_msubst_eval_lvalue
    | simple apply clean_LOCAL_right_eval_expr; solve_msubst_eval_expr
    | simple apply clean_LOCAL_right_andp; solve_clean_LOCAL_right
    | simple apply clean_LOCAL_right_tc_andp; solve_clean_LOCAL_right
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
    | fail 1000 "The right hand side is messed up; perhaps you inadvertently did something like 'simpl in *' that changes POSTCONDITION into a form that Floyd cannot recognize.  You may do 'unfold abbreviate in POSTCONDITION' in your previous proof steps to inspect it"
    ].

Inductive bangbang : Prop := bangbang_i.

(* The trick here is that if there is a "bangbang" hypothesis above the line,
 then eapply_clean_LOCAL_right_spec_rec will use the _bangbang form
 of the clean_LOCAL_right_spec lemma; otherwise the default version *)
Ltac choose_clean_LOCAL_right_spec L :=
 lazymatch goal with 
 | H: bangbang |- _ => eapply (clean_LOCAL_right_spec_bangbang L)
 | |- _ => eapply (clean_LOCAL_right_spec L)
 end.

Ltac eapply_clean_LOCAL_right_spec_rec gv L :=
  match goal with
  | |- context [gv ?i] =>
      match L with
      | context [i] => fail 1
      | _ => eapply_clean_LOCAL_right_spec_rec gv (@cons ident i L)
      end
  | _ := gv ?i |- _ =>
      match L with
      | context [i] => fail 1
      | _ => eapply_clean_LOCAL_right_spec_rec gv (@cons ident i L)
      end
  | _ => match goal with
         | |- _ ⊢ |==> _ => eapply (@clean_LOCAL_right_bupd_spec L)
         | _ => choose_clean_LOCAL_right_spec L
         end
  end.

Definition emptyCS : compspecs.
assert (composite_env_consistent (PTree.empty _)).
 hnf; intros; rewrite -> PTree.gempty in *; discriminate.
assert (composite_env_complete_legal_cosu_type (PTree.empty _)).
 hnf; intros; rewrite -> PTree.gempty in *; discriminate.
assert (hardware_alignof_env_consistent (PTree.empty _) (PTree.empty _)).
 hnf; intros; rewrite -> PTree.gempty in *; discriminate.
assert (hardware_alignof_env_complete (PTree.empty _) (PTree.empty _)).
 hnf; intros; rewrite -> PTree.gempty in *;
split; intros [? ?]; rewrite -> PTree.gempty in *; discriminate.
assert (legal_alignas_env_consistent (PTree.empty _) (PTree.empty _) (PTree.empty _)).
 hnf; intros; rewrite -> PTree.gempty in *; discriminate.
assert (legal_alignas_env_complete (PTree.empty _) (PTree.empty _)).
 hnf; intros; rewrite -> PTree.gempty in *;
split; intros [? ?]; rewrite -> PTree.gempty in *; discriminate.
refine (mkcompspecs (PTree.empty _) _ _ _ (PTree.empty _) _ _ (PTree.empty _) _ _ _); auto.
 hnf; intros; rewrite -> PTree.gempty in *; discriminate.
apply legal_alignas_soundness; auto.
Defined.

Ltac eapply_clean_LOCAL_right_spec :=
   match goal with
   | |- context [gvars ?gv] => 
          eapply_clean_LOCAL_right_spec_rec gv (@nil ident)
   | _ => match goal with
         | |- _ ⊢ |==> _ => eapply (clean_LOCAL_right_bupd_spec (@nil ident))
         | _ => choose_clean_LOCAL_right_spec (@nil ident)
         end
  end.

Ltac simpl_app_localdefs_tc :=
  unfold localdefs_tc, localdef_tc;
  unfold VST_floyd_map, VST_floyd_concat, VST_floyd_app;
  cbv iota zeta beta;
  simpl_temp_types_get;
  cbv iota zeta beta.

Ltac solve_all_legal_glob_ident :=
 reflexivity ||
lazymatch goal with
| gv: globals |- fold_right andb true (map ?F ?L) = true =>
  let L' := constr:(List.filter (Basics.compose negb F) L) 
  in let L' := eval simpl in L' 
  in fail 1 "The following global identifiers," L'
     "are not mentioned in your type-context,
therefore entailer or go_lower cannot operate on them."
"You can work around this problem by doing"
"(forget (" gv "i) as i')" "for each of those global identifiers i.
Then entailer or go_lower will work"
end.

Lemma assert_of_liftx_embed {Σ} P: assert_of(Σ:=Σ) (liftx P) ⊣⊢ ⎡P⎤.
Proof.
  intros.
  split => rho //; monPred.unseal; done.
Qed.

Ltac clean_LOCAL_canon_mix :=
  rewrite -?assert_of_liftx_embed; (* in case the goal has embed, which makes solve_clean_LOCAL_right fail *)
  eapply_clean_LOCAL_right_spec;
  [solve_all_legal_glob_ident | prove_local2ptree | solve_clean_LOCAL_right | simpl_app_localdefs_tc].

Lemma is_int_Vint_intro: forall sz sg v (P: Prop),
  ((exists i, v = Vint i /\ is_int sz sg (Vint i)) -> P) ->
  (is_int sz sg v -> P).
Proof.
  intros.
  apply H.
  destruct v; simpl in H0; try inv H0.
  eexists; eauto.
Qed.

Ltac intro_PROP :=
  match goal with
  | |- (tc_val ?t (Vint ?i)) -> ?P =>
          let Q := eval cbv beta iota zeta delta [tc_val] in (tc_val t (Vint i)) in
          change (Q -> P);
          fancy_intro true
  | |- (tc_val ?t ?v) -> ?P =>
          let t' := eval hnf in t in
          match t with
          | Tint ?sz ?sg _ =>
              is_var v;
              change (is_int sz sg v -> P);
              simple apply is_int_Vint_intro;
              let v' := fresh "v" in
              let tc := fresh "TC" in
              rename v into v';
              intros [v [? tc]];
              safe_subst v';
              revert tc; fancy_intro true
          | Tpointer ?t0 _ =>
              let b := eval hnf in (eqb_type t0 int_or_ptr_type) in
              match b with
              | true => change (is_pointer_or_integer v -> P); fancy_intro true
              | false => change (is_pointer_or_null v -> P); fancy_intro true
              end
          | _ => let Q := eval cbv beta iota zeta delta [tc_val] in (tc_val t v) in
                 change (Q -> P);
                 fancy_intro true
          end
  | |- (tc_val ?t ?v) -> ?P =>
         let Q := eval cbv beta iota zeta delta [tc_val] in (tc_val t v) in
         change (Q -> P);
         fancy_intro true
  | |- _ => fancy_intro true
  end.

Ltac check_mpreds R :=
 lazymatch R with
 | ?a :: ?al => match type of a with ?t =>
                          first [unify t mpred | fail 4 "The SEP conjunct" a "has type" t "but should have type mpred; these two types may be convertible but they are not identical"]
                     end; check_mpreds al
 | nil => idtac
 | _ => match type of R with ?t => 
               first [unify t (list mpred)
                      | fail 4 "The SEP list" R "has type" t "but should have type (list mpred); these two types may be convertible but they are not identical"]
            end
 end.

Ltac go_lower :=
clear_Delta_specs;
intros;
match goal with
 | |- local _ ∧ PROPx _ (LOCALx _ (SEPx ?R)) ⊢ _ => check_mpreds R
 | |- ENTAIL _, PROPx _ (LOCALx _ (SEPx ?R)) ⊢ _ => check_mpreds R
 | |- ENTAIL _, _ ⊢ _ => fail 10 "The left-hand-side of your entailment is not in PROP/LOCAL/SEP form"
 | _ => fail 10 "go_lower requires a proof goal in the form of (ENTAIL _ , _ ⊢ _)"
end;
clean_LOCAL_canon_mix;
repeat (simple apply derives_extract_PROP; intro_PROP);
let rho := fresh "rho" in
split => rho;
first
[ simple apply quick_finish_lower
|          
 (let TC := fresh "TC" in apply finish_lower; intros TC ||
 match goal with
 | |- (_ ∧ PROPx nil _) _ ⊢ _ => fail 1 "LOCAL part of precondition is not a concrete list (or maybe Delta is not concrete)"
 | |- _ => fail 1 "PROP part of precondition is not a concrete list"
 end);
cbv [fold_right_sepcon];
unfold_for_go_lower;
simpl tc_val;
cbv [typecheck_exprlist typecheck_expr]; simpl tc_andp;
simpl msubst_denote_tc_assert;
try monPred.unseal; unfold monPred_at;
try clear dependent rho;
clear_Delta;
rewrite ?bi.sep_emp
].

Ltac sep_apply_in_lifted_entailment H :=
 apply SEP_entail'; 
 go_lower; (* Using SEP_entail' and go_lower, instead of just SEP_entail,
     allows us to use propositional facts derived from the PROP and LOCAL
     parts of the left-hand side *)
(* unfold fold_right_sepcon at 1; *)
 match goal with |- ?R ⊢ ?R2 => 
  let r2 := fresh "R2" in pose (r2 := R2); change (R ⊢ r2);
  sep_apply_in_entailment H; [ .. | 
  match goal with |- ?R' ⊢ _ =>
   let R'' := refold_right_sepcon R' 
     in rewrite (_:R' ⊣⊢ fold_right_sepcon R'');
       [..| unfold fold_right_sepcon; rewrite ?bi.sep_emp; reflexivity ];
        subst r2; apply derives_refl
   end]
 end.

Ltac sep_apply_in_semax H :=
   eapply semax_pre(*_bupd*); [sep_apply_in_lifted_entailment H | ].

Ltac sep_apply H :=
 match goal with
 | |- ENTAIL _ , _ ⊢ _ => eapply ENTAIL_trans; [sep_apply_in_lifted_entailment H | ] 
 | |- _ ⊢ _ => sep_apply_in_entailment H
 | |- semax _ _ _ _ _ => sep_apply_in_semax H
 end.

Ltac new_sep_apply_in_lifted_entailment H evar_tac prop_tac :=
  apply SEP_entail';
  go_lower; (* Using SEP_entail' and go_lower, instead of just SEP_entail,
     allows us to use propositional facts derived from the PROP and LOCAL
     parts of the left-hand side *)
  (* unfold fold_right_sepcon at 1; *)
  match goal with |- ?R ⊢ ?R2 =>
    let r2 := fresh "R2" in pose (r2 := R2); change (R ⊢ r2);
    new_sep_apply_in_entailment H evar_tac prop_tac; [ .. |
    match goal with |- ?R' ⊢ _ =>
      let R'' := refold_right_sepcon R' in
      rewrite (_:R' ⊣⊢ fold_right_sepcon R'');
        [..| unfold fold_right_sepcon; rewrite ?bi.sep_emp; reflexivity ];
          subst r2; apply derives_refl
    end]
  end.

Ltac new_sep_apply_in_semax H evar_tac prop_tac :=
  eapply semax_pre(*_bupd*); [new_sep_apply_in_lifted_entailment H evar_tac prop_tac | ].

Ltac new_sep_apply H evar_tac prop_tac :=
  lazymatch goal with
  | |- ENTAIL _ , _ ⊢ _ => eapply ENTAIL_trans; [new_sep_apply_in_lifted_entailment H evar_tac prop_tac | ]
  | |- _ ⊢ _ => new_sep_apply_in_entailment H evar_tac prop_tac
  | |- semax _ _ _ _ _ => new_sep_apply_in_semax H evar_tac prop_tac
  end.

Ltac sep_apply_evar_tac x := fail 0 "Unable to find an instance for the variable" x.
Ltac default_sep_apply_prop_tac := first [reflexivity | assumption | idtac].
Ltac sep_apply_prop_tac := default_sep_apply_prop_tac.

Ltac sep_apply H ::=
  new_sep_apply H sep_apply_evar_tac sep_apply_prop_tac.

Ltac sep_eapply_evar_tac x := shelve.

Ltac sep_eapply_prop_tac := sep_apply_prop_tac.

Ltac sep_eapply H :=
  new_sep_apply H sep_eapply_evar_tac sep_apply_prop_tac.
