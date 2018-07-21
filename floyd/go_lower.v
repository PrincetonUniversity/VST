Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.semax_tactics.
Local Open Scope logic.

Ltac unfold_for_go_lower :=
  cbv delta [PROPx LOCALx SEPx locald_denote
                       eval_exprlist eval_expr eval_lvalue cast_expropt
                       sem_cast eval_binop eval_unop force_val1 force_val2
                      tc_expropt tc_expr tc_exprlist tc_lvalue tc_LR tc_LR_strong
                      typecheck_expr typecheck_exprlist typecheck_lvalue
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
  (temp_types Delta) ! i = Some (t,true) ->
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
apply tc_eval_id_i with Delta; auto.
Qed.

Lemma lower_one_temp_Vint:
 forall t rho Delta P i v Q R S,
  (temp_types Delta) ! i = Some (t,true) ->
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
  (temp_types Delta) ! i = Some (Tint sz sg noattr, true) ->
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
 | a : name ?i |- (local _ && PROPx _ (LOCALx (temp ?i ?v :: _) _)) _ |-- _ =>
     simple eapply lower_one_temp_Vint';
     [ reflexivity | ];
     let tc := fresh "TC" in
     clear a; intros [a [? [tc ?EVAL]]]; unfold tc_val in tc; try safe_subst v;
     revert tc; fancy_intro true
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
  (temp_types Delta) ! i = Some (t,true) ->
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
apply tc_eval_id_i with Delta; auto.
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
try match goal with |- ENTAIL (exit_tycon _ _ _), _ |-- _ =>
      simpl exit_tycon; simplify_Delta
  end;
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

Fixpoint extractp_localdef (x: localdef) (l: list localdef) : list Prop :=
  match l with
  | nil => nil
  | y :: l0 =>
     match x, y with
     | temp i u, temp j v =>
       if Pos.eqb i j
       then (u = v) :: extractp_localdef x l0
       else extractp_localdef x l0
     | lvar i ti u, lvar j tj v =>
       if Pos.eqb i j
       then (ti = tj) :: (u = v) :: extractp_localdef x l0
       else extractp_localdef x l0
     | _, _ => extractp_localdef x l0
     end
  end.

Definition localdef_tc (Delta: tycontext) (x: localdef): list Prop :=
  match x with
  | temp i v =>
      match (temp_types Delta) ! i with
      | Some (t,true) => tc_val t v :: nil
      | _ => nil
      end
  | lvar _ _ v =>
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
    destruct ((temp_types Delta) ! i) as [[? ?] |] eqn:?; simpl; auto.
    destruct b; simpl; auto.
    split; auto; eapply tc_eval_id_i; eauto.
  + simpl.
    assert (headptr v); [| split; [| split]; auto; apply headptr_isptr; auto].
    unfold lvar_denote in H0.
    destruct (Map.get (ve_of rho) i); [| inversion H0].
    destruct p, H0; subst.
    hnf; eauto.
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

Lemma go_lower_localdef_one_step_canon_both: forall Delta Ppre l Qpre Rpre Ppost Qpost Rpost,
  local (tc_environ Delta) && PROPx (Ppre ++ localdef_tc Delta l) (LOCALx Qpre (SEPx Rpre)) |--
    PROPx (Ppost ++ extractp_localdef l Qpost) (LOCALx (remove_localdef l Qpost) (SEPx Rpost)) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx (l :: Qpre) (SEPx Rpre)) |--
    PROPx Ppost (LOCALx Qpost (SEPx Rpost)).
Proof.
  intros.
  apply go_lower_localdef_one_step_canon_left.
  replace (PROPx (Ppost ++ extractp_localdef l Qpost)) with (PROPx (extractp_localdef l Qpost ++ Ppost)) in H.
  Focus 2. {
    apply PROPx_Permutation.
    apply Permutation_app_comm.
  } Unfocus.
  induction Qpost.
  + rewrite <- insert_local'.
    eapply derives_trans; [| apply H].
    solve_andp.
  + rewrite <- (insert_local' a).
    eapply derives_trans; [| apply andp_derives; [apply derives_refl | apply IHQpost]];
    clear IHQpost.
    - apply andp_right; [| auto].
      rewrite <- (insert_local' l).
      rewrite <- andp_assoc, (andp_comm _ (local _)),
              <- (andp_dup (local (tc_environ Delta))), <- andp_assoc,
              (andp_assoc _ _ (PROPx _ _)).
      eapply derives_trans; [apply andp_derives; [apply derives_refl | apply H] | clear H].
      simpl extractp_localdef; simpl remove_localdef.
      destruct l, a; try pos_eqb_tac;
        try (rewrite <- insert_local'; solve_andp);
        try (rewrite (andp_comm _ (local _)), andp_assoc, insert_local';
             rewrite <- !app_comm_cons;
             repeat (simple apply derives_extract_PROP; intros);
             subst; rewrite <- insert_local'; solve_andp).
    - rewrite <- (andp_dup (local (tc_environ Delta))), andp_assoc.
      eapply derives_trans; [apply andp_derives; [apply derives_refl | apply H] | clear H].
      simpl extractp_localdef; simpl remove_localdef.
      destruct l, a; try pos_eqb_tac;
      rewrite <- ?app_comm_cons, <- ?app_comm_cons, <- ?insert_local';
      repeat (simple apply derives_extract_PROP; intros);
      solve_andp.
Qed.

Definition re_localdefs (Pre Post: list localdef): list (list Prop) * list localdef :=
  fold_left (fun (PQ: list (list Prop) * list localdef) l => let (P, Q) := PQ in (extractp_localdef l Q :: P, remove_localdef l Q)) Pre (nil, Post).

Definition remove_localdefs (Pre Post: list localdef): list localdef :=
  match re_localdefs Pre Post with
  | (_, Q) => Q
  end.

Definition extractp_localdefs (Pre Post: list localdef): list Prop :=
  match re_localdefs Pre Post with
  | (P, _) => concat (rev P)
  end.

Definition localdefs_tc (Delta: tycontext) (Pre: list localdef): list Prop :=
  concat (map (localdef_tc Delta) Pre).

Lemma remove_localdefs_cons: forall a Qpre Qpost,
  remove_localdefs (a :: Qpre) Qpost = remove_localdefs Qpre (remove_localdef a Qpost).
Proof.
  intros.
  unfold remove_localdefs, re_localdefs; simpl.
  forget (extractp_localdef a Qpost :: nil) as P'.
  forget (@nil (list Prop)) as Q'.
  revert P' Q' a Qpost; induction Qpre; intros.
  * auto.
  * simpl.
    apply IHQpre.
Qed.

Lemma extractp_localdefs_cons: forall a Qpre Qpost,
  Permutation (extractp_localdefs (a :: Qpre) Qpost)
    (extractp_localdef a Qpost ++ extractp_localdefs Qpre (remove_localdef a Qpost)).
Proof.
  intros.
  unfold extractp_localdefs, re_localdefs; simpl.
  forget (remove_localdef a Qpost) as Q.
  pose proof Permutation_refl (extractp_localdef a Qpost :: nil).
  revert H.
  generalize (extractp_localdef a Qpost :: nil) at 1 3; intros P1.
  generalize (@nil (list Prop)) at 1 2; intros P2.
  revert P1 P2 Q; induction Qpre; intros.
  + simpl.
    apply Permutation_rev' in H.
    rewrite <- (Permutation_rev (_ :: _)) in H.
    apply Permutation_concat in H.
    rewrite H; clear H.
    simpl.
    apply Permutation_app_head, Permutation_concat, Permutation_rev.
  + simpl.
    apply IHQpre.
    rewrite perm_swap.
    apply perm_skip.
    auto.
Qed.

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

Lemma go_lower_localdef_canon_both: forall Delta Ppre Qpre Rpre Ppost Qpost Rpost,
  local (tc_environ Delta) && PROPx (Ppre ++ localdefs_tc Delta Qpre) (LOCALx nil (SEPx Rpre)) |--
    PROPx (Ppost ++ extractp_localdefs Qpre Qpost) (LOCALx (remove_localdefs Qpre Qpost) (SEPx Rpost)) ->
  local (tc_environ Delta) && PROPx Ppre (LOCALx Qpre (SEPx Rpre)) |--
    PROPx Ppost (LOCALx Qpost (SEPx Rpost)).
Proof.
  intros.
  revert Ppre Ppost Qpost H; induction Qpre; intros.
  + cbv [remove_localdefs extractp_localdefs localdefs_tc re_localdefs fold_left concat rev map] in H.
    rewrite !app_nil_r in H; auto.
  + apply go_lower_localdef_one_step_canon_both.
    apply IHQpre.
    rewrite <- !app_assoc.
    eapply derives_trans; [exact H |].
    clear.
    rewrite <- remove_localdefs_cons.
    erewrite PROPx_Permutation; [apply derives_refl |].
    apply Permutation_app_head.
    apply extractp_localdefs_cons.
Qed.

Ltac unfold_localdef_name QQ Q :=
  match Q with
  | nil => idtac
  | cons ?Qh ?Qt =>
    match Qh with
    | temp ?n _ => unfold n in QQ
    | lvar ?n _ _ => unfold n in QQ
    end;
    unfold_localdef_name QQ Qt
  end.

Ltac symbolic_go_lower :=
  match goal with
  | |- _ |-- PROPx _ (LOCALx _ (SEPx _)) =>
         apply go_lower_localdef_canon_both;
         (let el := fresh "el" in
         let rl := fresh "rl" in
         let PP := fresh "P" in
         let QQ := fresh "Q" in
         let PPr := fresh "Pr" in
         match goal with
         | |- context [?Pr ++ extractp_localdefs ?P ?Q] =>
                set (el := Pr ++ extractp_localdefs P Q);
                set (rl := remove_localdefs P Q);
                set (PPr := Pr) in el;
                set (PP := P) in el, rl;
                set (QQ := Q) in el, rl;
                cbv [re_localdefs extractp_localdefs remove_localdefs extractp_localdef remove_localdef concat rev fold_left app Pos.eqb] in el, rl;
                unfold_localdef_name PP P;
                unfold_localdef_name QQ Q;
                subst PPr PP QQ;
                cbv beta iota zeta in el, rl;
                subst el rl
         end);
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
         end)
  | |- _ |-- _ => idtac
  end.

