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

Lemma gvars_denote_HP: forall rho Delta gv i t,
  gvars_denote gv rho ->
  tc_environ Delta rho ->
  (glob_types Delta) ! i = Some t ->
  headptr (gv i).
Proof.
  intros.
  hnf in H.
  subst.
  destruct_glob_types i.
  rewrite Heqo0.
  hnf; eauto.
Qed.

Lemma lower_one_gvars:
 forall  rho Delta P gv Q R S,
  ((forall i t, (glob_types Delta) ! i = Some t -> headptr (gv i)) -> gvars_denote gv rho ->
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
  apply H; auto.
  intros.
  eapply gvars_denote_HP; eauto.
Qed.

Lemma finish_lower:
  forall rho (D: environ -> Prop) R S,
  (D rho -> fold_right_sepcon R |-- S) ->
  (local D && PROP() LOCAL() (SEPx R)) rho |-- S.
Proof.
intros.
simpl.
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

Ltac safe_subst x := subst x.
Ltac safe_subst_any := subst_any.
(* safe_subst is meant to avoid doing rewrites or substitution of variables that
  are in the scope of a unification variable.  Right now, the tactic is a placeholder
  for real tactic that will detect the scope violation and (if so) avoid doing the
  substition.  See issue #186. *)

Ltac lower_one_temp_Vint' :=
 match goal with
 | |- (local _ && PROPx _ (LOCALx (temp _ ?v :: _) _)) _ |-- _ =>
    is_var v;
     simple eapply lower_one_temp_Vint';
     [ reflexivity | ];
    let v' := fresh "v" in rename v into v';
     let tc := fresh "TC" in
     intros [v [? [tc ?EVAL]]]; unfold tc_val in tc; safe_subst v';
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

Ltac go_lower :=
intros;
match goal with
(* | |- ENTAIL ?D, normal_ret_assert _ _ _ |-- _ =>
       apply ENTAIL_normal_ret_assert; fancy_intros true
*)
 | |- local _ && _ |-- _ => idtac
 | |- ENTAIL _, _ |-- _ => idtac
 | _ => fail 10 "go_lower requires a proof goal in the form of (ENTAIL _ , _ |-- _)"
end;
repeat (simple apply derives_extract_PROP; fancy_intro true);
let rho := fresh "rho" in
intro rho;
first [simple apply quick_finish_lower
| repeat first
 [ simple eapply lower_one_temp_Vint;
     [try reflexivity; solve [eauto] | fancy_intro true; intros ?EVAL ]
 | lower_one_temp_Vint'
 | simple eapply lower_one_temp;
     [try reflexivity; solve [eauto] | fancy_intro true; intros ?EVAL]
 | simple apply lower_one_lvar;
     fold_types1; fancy_intro true; intros ?LV
 | match goal with
   | |- (_ && PROPx _ (LOCALx (gvars ?gv :: _) (SEPx _))) _ |-- _ =>
     simple eapply lower_one_gvars;
     let HH := fresh "HHH" in
     intros HH ?GV;
     gvar_headptr_intro gv HH;
     clear HH
   end
 ];
 ((let TC := fresh "TC" in simple apply finish_lower; intros TC) ||
 match goal with
 | |- (_ && PROPx nil _) _ |-- _ => fail 1 "LOCAL part of precondition is not a concrete list (or maybe Delta is not concrete)"
 | |- _ => fail 1 "PROP part of precondition is not a concrete list"
 end);
unfold_for_go_lower;
simpl; rewrite ?sepcon_emp;
repeat match goal with
| H: eval_id ?i rho = ?v |- _ =>
 first [rewrite ?H in *; clear H; match goal with
               | H:context[eval_id i rho]|-_ => fail 2
               | |- _ => idtac
               end
        |  let x := fresh "x" in
             set (x := eval_id i rho) in *; clearbody x; subst x
        ]
end;
repeat match goal with
 | H: lvar_denote ?i ?t ?v rho |- context [lvar_denote ?i ?t' ?v' rho] =>
     rewrite (eq_True (lvar_denote i t' v' rho) H)
 | H: gvars_denote ?gv rho |- context [gvars_denote ?gv rho] =>
     rewrite (eq_True (gvars_denote gv rho) H)
end;
repeat match goal with
 | H: lvar_denote ?i ?t ?v rho |- context [eval_var ?i ?t rho] =>
     rewrite (lvar_eval_var i t v rho H)
end;
repeat match goal with
 | H: gvars_denote ?gv rho |- context [eval_var ?i ?t rho] =>
     erewrite (gvars_eval_var _ gv i rho t); [| eassumption | reflexivity | exact H]
end
];
clear_Delta_specs;
clear_Delta;
try clear dependent rho;
simpl.

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
      match (temp_types Delta) ! i with
      | Some t => tc_val t v :: nil
      | _ => nil
      end
  | lvar _ _ v =>
      isptr v :: headptr v :: nil
  | gvars gv =>
      map (fun id => headptr (gv id)) gvar_idents
  end.

Ltac pos_eqb_tac :=
  let H := fresh "H" in
  match goal with
  | |- context [Pos.eqb ?i ?j] => destruct (Pos.eqb i j) eqn:H; [apply Pos.eqb_eq in H | apply Pos.eqb_neq in H]
  end.

Definition legal_glob_ident (Delta: tycontext) (i: ident): bool :=
  match (glob_types Delta) ! i with
  | Some _ => true
  | _ => false
  end.

Lemma localdef_local_facts: forall Delta gvar_ident x,
  fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true ->
  local (tc_environ Delta) && local (locald_denote x) |-- !! fold_right and True (localdef_tc Delta gvar_ident x).
Proof.
  intros.
  rename H into LEGAL.
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
  + unfold localdef_tc.
    induction gvar_ident; [exact I |].
    simpl in LEGAL.
    rewrite andb_true_iff in LEGAL.
    destruct LEGAL as [LEGAL0 LEGAL].
    split; [clear IHgvar_ident | apply IHgvar_ident; auto].
    unfold gvars_denote in H0.
    subst g.
    unfold legal_glob_ident in LEGAL0.
    destruct_glob_types a.
      2: rewrite Heqo in LEGAL0; inv LEGAL0.
    rewrite Heqo0.
    hnf; eauto.  
Qed.

Lemma go_lower_localdef_one_step_canon_left: forall Delta Ppre l Qpre Rpre post gvar_ident
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local (tc_environ Delta) && PROPx (Ppre ++ localdef_tc Delta gvar_ident l) (LOCALx (l :: Qpre) (SEPx Rpre)) |-- post ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx (l :: Qpre) (SEPx Rpre)) |-- post.
Proof.
  intros.
  apply derives_trans with (local (tc_environ Delta) && PROPx (Ppre ++ localdef_tc Delta gvar_ident l) (LOCALx (l :: Qpre) (SEPx Rpre))); auto.
  replace (PROPx (Ppre ++ localdef_tc Delta gvar_ident l)) with (PROPx (localdef_tc Delta gvar_ident l ++ Ppre)).
  2:{
    apply PROPx_Permutation.
    apply Permutation_app_comm.
  }
  rewrite <- !insert_local'.
  apply andp_right; [solve_andp |].
  apply andp_right; [solve_andp |].
  unfold PROPx. apply andp_right; [| solve_andp].
  rewrite <- andp_assoc.
  eapply derives_trans; [apply andp_derives; [apply localdef_local_facts; eauto | apply derives_refl] |].
  rewrite <- andp_assoc.
  apply andp_left1.
  remember (localdef_tc Delta gvar_ident l); clear.
  induction l0.
  + simpl fold_right.
    apply andp_left2; auto.
  + simpl fold_right.
    rewrite !prop_and, !andp_assoc.
    apply andp_derives; auto.
Qed.

Definition localdefs_tc (Delta: tycontext) gvar_ident (Pre: list localdef): list Prop :=
  concat (map (localdef_tc Delta gvar_ident) Pre).

Lemma go_lower_localdef_canon_left: forall Delta Ppre Qpre Rpre post gvar_ident
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local (tc_environ Delta) && PROPx (Ppre ++ localdefs_tc Delta gvar_ident Qpre) (LOCALx nil (SEPx Rpre)) |-- post ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) |-- post.
Proof.
  intros.
  revert Ppre post H; induction Qpre; intros.
  + cbv [localdefs_tc concat rev map] in H.
    rewrite !app_nil_r in H; auto.
  + eapply go_lower_localdef_one_step_canon_left; eauto.
    rewrite <- insert_local, (andp_comm _ (PROPx _ _)), <- andp_assoc, -> imp_andp_adjoint.
    apply IHQpre.
    rewrite <- imp_andp_adjoint.
    apply andp_left1.
    rewrite <- !app_assoc.
    eapply derives_trans; [exact H | auto].
Qed.

Definition msubst_extract_local (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) (x: localdef): Prop :=
  match x with
  | temp i u =>
    match T1 ! i with
    | Some v => u = v
    | None => False
    end
  | lvar i ti u =>
    match T2 ! i with
    | Some (tj, v) =>
      if eqb_type ti tj
      then u = v
      else False
    | _ => False
    end
  | gvars gv =>
    match GV with
    | Some gv0 => gv0 = gv
    | _ => False
    end
  end.

Definition msubst_extract_locals (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) := map (msubst_extract_local Delta T1 T2 GV).

Lemma localdef_local_facts_inv: forall Delta P T1 T2 GV R x,
  msubst_extract_local Delta T1 T2 GV x ->
  local (tc_environ Delta) && PROPx P (LOCALx (LocalD T1 T2 GV) (SEPx R)) |-- local (locald_denote x).
Proof.
  intros.
  destruct x; simpl in H.
  + apply in_local.
    apply LocalD_sound_temp.
    destruct (T1 ! i); inv H; auto.
  + apply in_local.
    destruct (T2 ! i) as [[? ?] |] eqn:?H; try solve [inv H].
    destruct (eqb_type t t0) eqn:?H; [| inv H].
    apply eqb_type_spec in H1; subst.
    eapply LocalD_sound_local in H0.
    exact H0.
  + apply in_local.
    destruct GV as [? |] eqn:?H; try solve [inv H].
    subst g0 GV.
    apply LocalD_sound_gvars; auto.
Qed.

Lemma go_lower_localdef_one_step_canon_canon {cs: compspecs} : forall Delta Ppre Qpre Rpre Ppost l Qpost Rpost T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && PROPx (Ppost ++ msubst_extract_local Delta T1 T2 GV l :: nil) (LOCALx Qpost (SEPx Rpost)) |-- PROPx Ppost (LOCALx (l :: Qpost) (SEPx Rpost)).
Proof.
  intros.
  replace (PROPx (Ppost ++ msubst_extract_local Delta T1 T2 GV l :: nil)) with (PROPx (msubst_extract_local Delta T1 T2 GV l :: Ppost)).
  2:{
    apply PROPx_Permutation.
    eapply Permutation_trans; [| apply Permutation_app_comm].
    apply Permutation_refl.
  }
  rewrite <- !insert_local', <- !insert_prop.
  apply andp_right; [| solve_andp].
  normalize.
  apply andp_left1.
  apply (local2ptree_soundness Ppre _ Rpre) in H; simpl in H.
  rewrite H.
  apply localdef_local_facts_inv; auto.
Qed.

Lemma go_lower_localdef_canon_canon {cs: compspecs} : forall Delta Ppre Qpre Rpre Ppost Qpost Rpost T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && PROPx (Ppost ++ msubst_extract_locals Delta T1 T2 GV Qpost) (LOCALx nil (SEPx Rpost)) |-- PROPx Ppost (LOCALx Qpost (SEPx Rpost)).
Proof.
  intros.
  revert Ppost; induction Qpost; intros.
  + simpl app.
    rewrite app_nil_r.
    solve_andp.
  + eapply derives_trans; [| apply (go_lower_localdef_one_step_canon_canon Delta Ppre Qpre Rpre); eassumption].
    apply andp_right; [solve_andp |].
    eapply derives_trans; [| apply IHQpost].
    rewrite <- app_assoc; simpl app; auto.
Qed.

Lemma go_lower_localdef_canon_tc_expr {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_expr Delta T1 T2 GV e) |-- tc_expr Delta e.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_expr_sound.
Qed.

Lemma go_lower_localdef_canon_tc_lvalue {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_lvalue Delta T1 T2 GV e) |-- tc_lvalue Delta e.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_lvalue_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_LR {cs: compspecs} : forall Delta Ppre Qpre Rpre e lr T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_LR Delta T1 T2 GV e lr) |-- tc_LR Delta e lr.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_LR_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_efield {cs: compspecs} : forall Delta Ppre Qpre Rpre efs T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_efield Delta T1 T2 GV efs) |-- tc_efield Delta efs.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_efield_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_exprlist {cs: compspecs} : forall Delta Ppre Qpre Rpre ts es T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_exprlist Delta T1 T2 GV ts es) |-- tc_exprlist Delta ts es.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_exprlist_sound; auto.
Qed.

Lemma go_lower_localdef_canon_tc_expropt {cs: compspecs} : forall Delta Ppre Qpre Rpre e t T1 T2 GV,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(msubst_tc_expropt Delta T1 T2 GV e t) |-- tc_expropt Delta e t.
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  apply msubst_tc_expropt_sound; auto.
Qed.

Lemma go_lower_localdef_canon_eval_lvalue {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV u v,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  msubst_eval_lvalue Delta T1 T2 GV e = Some u ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(!! (u = v)) |-- local (`(eq v) (eval_lvalue e)).
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  normalize.
  apply msubst_eval_lvalue_eq, H0.
Qed.

Lemma go_lower_localdef_canon_eval_expr {cs: compspecs} : forall Delta Ppre Qpre Rpre e T1 T2 GV u v,
  local2ptree Qpre = (T1, T2, nil, GV) ->
  msubst_eval_expr Delta T1 T2 GV e = Some u ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) && `(!! (u = v)) |-- local (`(eq v) (eval_expr e)).
Proof.
  intros.
  erewrite local2ptree_soundness by eassumption.
  normalize.
  apply msubst_eval_expr_eq, H0.
Qed.

Inductive clean_LOCAL_right {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals): (environ -> mpred) -> mpred -> Prop :=
| clean_LOCAL_right_sep_lift: forall P, clean_LOCAL_right Delta T1 T2 GV (`P) (P)
| clean_LOCAL_right_local_lift: forall P, clean_LOCAL_right Delta T1 T2 GV (local (`P)) (!! P)
| clean_LOCAL_right_prop: forall P, clean_LOCAL_right Delta T1 T2 GV (!! P) (!! P)
| clean_LOCAL_right_tc_lvalue: forall e, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_lvalue Delta e)) (msubst_tc_lvalue Delta T1 T2 GV e)
| clean_LOCAL_right_tc_expr: forall e, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_expr Delta e)) (msubst_tc_expr Delta T1 T2 GV e)
| clean_LOCAL_right_tc_LR: forall e lr, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_LR Delta e lr)) (msubst_tc_LR Delta T1 T2 GV e lr)
| clean_LOCAL_right_tc_efield: forall efs, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_efield Delta efs)) (msubst_tc_efield Delta T1 T2 GV efs)
| clean_LOCAL_right_tc_exprlist: forall ts es, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (typecheck_exprlist Delta ts es)) (msubst_tc_exprlist Delta T1 T2 GV ts es)
| clean_LOCAL_right_tc_expropt: forall e t, clean_LOCAL_right Delta T1 T2 GV (tc_expropt Delta e t) (msubst_tc_expropt Delta T1 T2 GV e t)
| clean_LOCAL_right_canon: forall P Q R, clean_LOCAL_right Delta T1 T2 GV (PROPx P (LOCALx Q (SEPx R))) (!! (fold_right and True (P ++ msubst_extract_locals Delta T1 T2 GV Q)) && fold_right_sepcon R)
| clean_LOCAL_right_eval_lvalue: forall e u v, msubst_eval_lvalue Delta T1 T2 GV e = Some u -> clean_LOCAL_right Delta T1 T2 GV (local (`(eq v) (eval_lvalue e))) (!! (u = v))
| clean_LOCAL_right_eval_expr: forall e u v, msubst_eval_expr Delta T1 T2 GV e = Some u -> clean_LOCAL_right Delta T1 T2 GV (local (`(eq v) (eval_expr e))) (!! (u = v))
| clean_LOCAL_right_andp: forall P1 P2 Q1 Q2, clean_LOCAL_right Delta T1 T2 GV P1 Q1 -> clean_LOCAL_right Delta T1 T2 GV P2 Q2 -> clean_LOCAL_right Delta T1 T2 GV (P1 && P2) (Q1 && Q2)
| clean_LOCAL_right_EX': forall A (P: A -> environ -> mpred) (Q: A -> mpred), (forall a, clean_LOCAL_right Delta T1 T2 GV (P a) (Q a)) -> clean_LOCAL_right Delta T1 T2 GV (exp P) (exp Q).

Lemma clean_LOCAL_right_TT {cs: compspecs} (Delta : tycontext) (T1 : PTree.t val) (T2 : PTree.t (type * val)) (GV : option globals): clean_LOCAL_right Delta T1 T2 GV TT TT.
Proof.
  intros.
  exact (clean_LOCAL_right_sep_lift _ _ _ _ TT).
Qed.

Lemma clean_LOCAL_right_FF {cs: compspecs} (Delta : tycontext) (T1 : PTree.t val) (T2 : PTree.t (type * val)) (GV : option globals): clean_LOCAL_right Delta T1 T2 GV FF FF.
Proof.
  intros.
  exact (clean_LOCAL_right_sep_lift _ _ _ _ FF).
Qed.

Lemma clean_LOCAL_right_tc_andp {cs: compspecs} (Delta : tycontext) (T1 : PTree.t val) (T2 : PTree.t (type * val)) (GV : option globals): forall P1 P2 Q1 Q2, clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert P1) Q1 -> clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert P2) Q2 -> clean_LOCAL_right Delta T1 T2 GV (denote_tc_assert (tc_andp P1 P2)) (Q1 && Q2).
Proof.
  intros.
  rewrite denote_tc_assert_andp.
  apply clean_LOCAL_right_andp; auto.
Qed.

Lemma clean_LOCAL_right_EX: forall {cs: compspecs} (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) A (P: A -> environ -> mpred) (Q: A -> mpred),
  (forall a, exists Q', clean_LOCAL_right Delta T1 T2 GV (P a) Q' /\ Q' = Q a) ->
  clean_LOCAL_right Delta T1 T2 GV (exp P) (exp Q).
Proof.
  intros.
  apply clean_LOCAL_right_EX'.
  intros; specialize (H a).
  destruct H as [? [? ?]].
  subst; auto.
Qed.

Lemma clean_LOCAL_right_aux: forall {cs: compspecs} gvar_ident (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) && ` S' |-- S.
Proof.
  intros.
  induction H0.
  + apply andp_left2. apply derives_refl.
  + apply andp_left2. apply derives_refl.
  + apply andp_left2. apply derives_refl.
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

Lemma clean_LOCAL_right_spec: forall {cs: compspecs} gvar_ident (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  local (tc_environ Delta) && PROPx (P ++ localdefs_tc Delta gvar_ident Q) (LOCALx nil (SEPx R)) |-- ` S' ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- S.
Proof.
  intros.
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- `S')
    by (eapply go_lower_localdef_canon_left; eauto).
  rewrite (add_andp _ _ H2); clear H1 H2.
  eapply clean_LOCAL_right_aux; eauto.
Qed.

Lemma clean_LOCAL_right_bupd_spec: forall {cs: compspecs} gvar_ident (Delta: tycontext) (T1: PTree.t val) (T2: PTree.t (type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  local (tc_environ Delta) && PROPx (P ++ localdefs_tc Delta gvar_ident Q) (LOCALx nil (SEPx R)) |-- |==> ` S' ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- |==> S.
Proof.
  intros.
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- |==> `S')
    by (eapply go_lower_localdef_canon_left; eauto).
  pose proof clean_LOCAL_right_aux _ _ _ _ _ P _ (TT :: nil) _ _ LEGAL H H0.
  rewrite (add_andp _ _ H2); clear H1 H2.
  eapply derives_trans.
  + apply andp_derives; [| apply derives_refl].
    apply andp_derives; [apply derives_refl |].
    instantiate (1 := PROPx P (LOCALx Q SEP (TT))).
    apply andp_derives; auto.
    apply andp_derives; auto.
    unfold SEPx; simpl.
    rewrite sepcon_emp; auto.
  + rewrite andp_comm.
    eapply derives_trans; [apply bupd_andp2_corable |].
    - apply corable_andp; [intro; apply corable_prop |].
      apply corable_andp; [intro; simpl; apply corable_prop |].
      apply corable_andp; [intro; simpl; apply corable_prop |].
      unfold SEPx; simpl.
      rewrite sepcon_emp.
      intro; simpl. apply corable_prop.
    - apply bupd_mono.
      rewrite andp_comm.
      auto.
Qed.

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

Ltac solve_clean_LOCAL_right :=
  solve
    [ simple apply clean_LOCAL_right_sep_lift
    | simple apply clean_LOCAL_right_local_lift
    | simple apply clean_LOCAL_right_prop
    | simple apply clean_LOCAL_right_TT
    | simple apply clean_LOCAL_right_FF
    | try unfold tc_lvalue; simple apply clean_LOCAL_right_tc_lvalue
    | try unfold tc_expr; simple apply clean_LOCAL_right_tc_expr
    | try unfold tc_LR; simple apply clean_LOCAL_right_tc_LR
    | try unfold tc_efield; simple apply clean_LOCAL_right_tc_efield
    | try unfold tc_exprlist; simple apply clean_LOCAL_right_tc_exprlist
    | simple apply clean_LOCAL_right_tc_expropt
    | simple apply clean_LOCAL_right_canon
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
         | |- _ |-- |==> _ => eapply (clean_LOCAL_right_bupd_spec L)
         | _ => eapply (clean_LOCAL_right_spec L)
         end
  end.

Ltac eapply_clean_LOCAL_right_spec :=
  match goal with
  | |- context [gvars ?gv] => eapply_clean_LOCAL_right_spec_rec gv (@nil ident)
  | _ => match goal with
         | |- _ |-- |==> _ => eapply (clean_LOCAL_right_bupd_spec nil)
         | _ => eapply (clean_LOCAL_right_spec nil)
         end
  end.

Ltac elim_temp_types_get v :=
  revert v;
  match goal with
  | |- let _ := ?e in _ =>
      match e with
      | context [(temp_types ?Delta) ! ?i] =>
          let ret := eval hnf in ((temp_types Delta) ! i) in
          intro v;  
          change ((temp_types Delta) ! i) with ret in (value of v)
      end
  end.

Ltac clean_LOCAL_canon_mix :=
  eapply_clean_LOCAL_right_spec;
    [reflexivity | prove_local2ptree | solve_clean_LOCAL_right |];
         let tl := fresh "tl" in
         let QQ := fresh "Q" in
         let PPr := fresh "Pr" in
         match goal with
         | |- context [?Pr ++ localdefs_tc ?Delta ?gvar_ident ?Q] =>
                set (tl := Pr ++ localdefs_tc Delta gvar_ident Q);
                set (PPr := Pr) in tl;
                set (QQ := Q) in tl;
                cbv [localdefs_tc localdef_tc concat map app] in tl;
                subst PPr QQ;
                cbv beta iota zeta in tl;
                repeat elim_temp_types_get tl;
                cbv beta iota zeta in tl;
                subst tl
         end.

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

Ltac go_lower ::=
clear_Delta_specs;
intros;
match goal with
(* | |- ENTAIL ?D, normal_ret_assert _ _ _ |-- _ =>
       apply ENTAIL_normal_ret_assert; fancy_intros true
*)
 | |- local _ && _ |-- _ => idtac
 | |- ENTAIL _, _ |-- _ => idtac
 | _ => fail 10 "go_lower requires a proof goal in the form of (ENTAIL _ , _ |-- _)"
end;
clean_LOCAL_canon_mix;
repeat (simple apply derives_extract_PROP; intro_PROP);
let rho := fresh "rho" in
intro rho;
first
[ simple apply quick_finish_lower
|          
 (let TC := fresh "TC" in simple apply finish_lower; intros TC ||
 match goal with
 | |- (_ && PROPx nil _) _ |-- _ => fail 1 "LOCAL part of precondition is not a concrete list (or maybe Delta is not concrete)"
 | |- _ => fail 1 "PROP part of precondition is not a concrete list"
 end);
unfold_for_go_lower;
simpl;
try (progress unfold_for_go_lower; simpl); rewrite ?sepcon_emp;
clear_Delta;
try clear dependent rho].
