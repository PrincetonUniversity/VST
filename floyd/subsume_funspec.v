Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Local Open Scope logic.

Definition funsig_of_funspec (fs: funspec) : funsig :=
 match fs with mk_funspec fsig _ _ _ _ _ _ => fsig end.

Definition params_of_funspec (fs: funspec) : list (ident * type) :=
  fst (funsig_of_funspec fs).

Definition return_of_funspec (fs: funspec) : type :=
  snd (funsig_of_funspec fs).

Definition funsig_tycontext (fs: funsig) : tycontext :=
  make_tycontext (fst fs) nil nil (snd fs) nil nil nil.

Definition funsig_of_function (f: function) : funsig :=
  (fn_params f, fn_return f).

(* If we were to require that a non-void-returning function must,
   at a function call, have its result assigned to a temp,
   then we could change "ret0_tycon" to "ret_tycon" in this
   definition (and in NDsubsume_funspec). *)
Definition subsume_funspec (f1 f2 : funspec) :=
 let Delta := (funsig_tycontext (funsig_of_funspec f1)) in
 match f1 with
 | mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
   fsig1 = fsig2 /\ cc1 = cc2 /\
     forall ts2 x2, 
        ENTAIL Delta, P2 ts2 x2 |-- EX ts1: list Type, EX x1:_, EX F:mpred,
                             ((`F * P1 ts1 x1) &&
                             (!! (ENTAIL (ret0_tycon Delta), `F * Q1 ts1 x1 
                                          |-- Q2 ts2 x2)))
  end end.

Definition NDsubsume_funspec (f1 f2 : funspec) :=
 let Delta := (funsig_tycontext (funsig_of_funspec f1)) in
 match f1 with
 | mk_funspec fsig1 cc1 (rmaps.ConstType A1) P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 (rmaps.ConstType A2) P2 Q2 _ _ =>
   fsig1 = fsig2 /\ cc1 = cc2 /\  forall x2,
        ENTAIL Delta, P2 nil x2 |-- EX x1:_, EX F:mpred,
                             ((`F * P1 nil x1) &&
                             (!! (ENTAIL (ret0_tycon Delta), `F * Q1 nil x1 
                                      |-- Q2 nil x2)))
 | _ => False end
 | _ => False end.

Definition is_NDfunspec (fs: funspec) :=
 match fs with
 | mk_funspec _ _ (rmaps.ConstType A) P Q _ _ =>
    (forall ts, P ts = P nil /\ Q ts = Q nil)
 | _ => False
 end.

Lemma NDsubsume_subsume:
  forall f1 f2, 
   is_NDfunspec f2 ->
   NDsubsume_funspec f1 f2 ->
   subsume_funspec f1 f2.
Proof.
intros f1 f2. pose proof I. intros H0 H1.
destruct f1, f2; hnf in H1.
destruct A; try contradiction. destruct A0; try contradiction.
destruct H1 as [? [? ?]]; split3; auto.
subst f0 c0.
intros ts1 x1.
specialize (H3 x1).
simpl in H0.
specialize (H0 ts1). destruct H0 as [H0 H0'].
rewrite H0.
eapply derives_trans; [apply H3 | clear H3 ].
Intros x2 F.
Exists (@nil Type) x2 F.
apply andp_right; auto.
apply prop_right.
rewrite H0'. auto.
Qed.

Inductive empty_type : Type := .

Definition withtype_of_NDfunspec fs := match fs with
  mk_funspec _ _ (rmaps.ConstType A) _ _ _ _ => A | _ => empty_type end.
 

Definition withtype_of_funspec fs := match fs with
  mk_funspec _ _ A _ _ _ _ => A end.

Lemma tc_val_sem_cast':
  forall {CS: compspecs} t2 e2 rho Delta,
      typecheck_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho
     &&  denote_tc_assert (isCastResultType (typeof e2) t2  e2) rho 
     |-- !! tc_val t2 (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho))).
Proof.
intros.
Transparent Nveric.
intro phi.
intros [? ?].
do 6 red.
Opaque Nveric.
eapply expr_lemmas.tc_val_sem_cast; eauto.
Qed.

Lemma subsume_funspec_refl:
  forall fs, subsume_funspec fs fs.
Proof.
intros.
destruct fs; simpl.
split3; auto.
intros.
Exists ts2.
Exists x2. Exists emp.
unfold_lift.
rewrite !emp_sepcon.
apply andp_right.
apply andp_left2; auto.
apply prop_right.
intros rho'.
rewrite emp_sepcon.
apply andp_left2; auto.
Qed.


Lemma sepcon_ENTAIL:
 forall Delta P Q P' Q',
  ENTAIL Delta, P |-- P' ->
  ENTAIL Delta, Q |-- Q' ->
  ENTAIL Delta, P * Q |-- P' * Q'.
Proof.
intros.
intro rho; specialize (H rho); specialize (H0 rho); simpl in *.
unfold local, lift1 in *.
normalize.
rewrite prop_true_andp in H,H0 by auto.
apply sepcon_derives; auto.
Qed.

Lemma subsume_funspec_trans:
  forall fs1 fs2 fs3, 
    subsume_funspec fs1 fs2 ->
    subsume_funspec fs2 fs3 ->
    subsume_funspec fs1 fs3.
Proof.
intros.
destruct fs1 as [f1 c1 A1 P1 Q1 Pne1 Qne1].
destruct fs2 as [f2 c2 A2 P2 Q2 Pne2 Qne2].
destruct fs3 as [f3 c3 A3 P3 Q3 Pne3 Qne3].
destruct H as [H' [H'' H]].
destruct H0 as [H0' [H0'' H0]].
subst f3 c3. subst f2 c2.
split3; auto.
intros ts3 x3.
change
  (functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts3 A3) mpred)
  in x3.
specialize (H0 ts3 x3).
eapply ENTAIL_trans; [apply H0 | ].
clear H0.
Intros ts2 x2 F.
change
  (functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts2 A2) mpred)
  in x2.
specialize (H ts2 x2).
eapply derives_trans.
apply sepcon_ENTAIL.
apply ENTAIL_refl.
apply H.
clear H.
Intros ts1 x1.
change
  (functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts1 A1) mpred)
  in x1.
Intros F1.
Exists ts1 x1 (F*F1).
apply andp_right.
intro rho.
unfold_lift. unfold local, lift1. simpl. normalize.
rewrite sepcon_assoc. auto.
apply prop_right.
apply ENTAIL_trans with (`F * (`F1 * Q1 ts1 x1)).
apply andp_left2.
clear. unfold_lift; intro rho; simpl. rewrite sepcon_assoc; auto.
simpl funsig_tycontext in *.
eapply ENTAIL_trans; [ | apply H0].
apply sepcon_ENTAIL.
apply ENTAIL_refl.
 auto.
Qed.

Lemma NDsubsume_funspec_refl:
  forall fsig cc A P Q, 
   NDsubsume_funspec (NDmk_funspec fsig cc A P Q) (NDmk_funspec fsig cc A P Q).
Proof.
intros.
simpl.
split3; auto.
intros.
Exists x2. Exists emp.
unfold_lift.
rewrite !emp_sepcon.
apply andp_right.
apply andp_left2; auto.
apply prop_right.
intros rho'.
rewrite emp_sepcon.
apply andp_left2; auto.
Qed.

Lemma NDsubsume_funspec_trans:
  forall fsig1 cc1 A1 P1 Q1 fsig2 cc2 A2 P2 Q2 fsig3 cc3 A3 P3 Q3, 
   NDsubsume_funspec (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig2 cc2 A2 P2 Q2) ->
   NDsubsume_funspec (NDmk_funspec fsig2 cc2 A2 P2 Q2) (NDmk_funspec fsig3 cc3 A3 P3 Q3) ->
   NDsubsume_funspec (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig3 cc3 A3 P3 Q3).
Proof.
intros.
destruct H as [?E [?E H]]. 
destruct H0 as [?E [?E H0]].
subst.
split3; auto.
intro x3; simpl in x3.
specialize (H0 x3).
eapply ENTAIL_trans; [apply H0 | ].
clear H0.
Intros x2 F.
simpl in x2.
specialize (H x2).
eapply derives_trans.
apply sepcon_ENTAIL.
apply ENTAIL_refl.
apply H.
clear H.
Intros x1. simpl in x1.
Intros F1.
Exists x1 (F*F1).
apply andp_right.
intro rho.
unfold_lift. unfold local, lift1. simpl. normalize.
rewrite sepcon_assoc. auto.
apply prop_right.
apply ENTAIL_trans with (`F * (`F1 * Q1 x1)).
apply andp_left2.
clear. unfold_lift; intro rho; simpl. rewrite sepcon_assoc; auto.
simpl funsig_tycontext in *.
eapply ENTAIL_trans; [ | apply H0].
apply sepcon_ENTAIL.
apply ENTAIL_refl.
 auto.
Qed.

Lemma tc_environ_make_args':
 forall {CS: compspecs} argsig retsig bl rho Delta,
   tc_environ Delta rho ->
  tc_exprlist Delta (snd (split argsig)) bl rho
  |-- !! tc_environ (funsig_tycontext (argsig, retsig))
          (make_args' (argsig, retsig)
            (eval_exprlist (snd (split argsig)) bl) rho).
Proof.
intros. rename H into H2.
unfold tc_environ, make_args'.
simpl.
unfold tc_exprlist.
revert bl; induction argsig; destruct bl as [ | b bl]; simpl; intros; unfold_lift.
*
apply prop_right. split3; hnf; intros; try (simpl in *; rewrite PTree.gempty in H; inv H).
rewrite PTree.gempty. split; intro. inv H. destruct H. inv H.
*
apply prop_derives; intros. inv H.
*
destruct a as [i ti]; simpl.
destruct (split argsig) eqn:?.
simpl.
unfold_lift; apply prop_derives; intros; inv H.
*
destruct a as [i ti]; simpl.
destruct (split argsig) eqn:?.
specialize (IHargsig bl).
simpl denote_tc_assert.
rewrite !denote_tc_assert_andp.
simpl andp.
unfold_lift.
apply derives_trans with
 (denote_tc_assert (typecheck_expr Delta b) rho &&
 denote_tc_assert (isCastResultType (typeof b) ti b) rho &&
 (!! typecheck_environ (funsig_tycontext (argsig, retsig))
                    (make_args (map fst argsig)
                       (eval_exprlist l0 bl rho) rho))).
apply andp_derives; auto.
clear IHargsig.
simpl. unfold_lift.
normalize.
destruct H as [? [? ?]].
unfold typecheck_environ; simpl.
match goal with |- ?A |-- ?B => apply derives_trans with
    (!! tc_val' ti (force_val (sem_cast (typeof b) ti (eval_expr b rho))) && A)
end.
apply andp_right; auto.
clear - H2.
apply derives_trans with 
 (!! (tc_val (typeof b) (eval_expr b rho)) &&
   !! (tc_val ti (force_val (sem_cast (typeof b) ti (eval_expr b rho))))).
apply andp_right.
eapply derives_trans; [ | eapply typecheck_expr_sound]; eauto.
apply andp_left1. apply derives_refl.
pose proof expr_lemmas.tc_val_sem_cast.
apply tc_val_sem_cast'; auto.
apply andp_left2.
apply prop_derives.
unfold tc_val'.
intros; auto.
normalize. rename H3 into H8.
apply prop_right.
split3; auto.
unfold typecheck_temp_environ; intros.
destruct (ident_eq i id).
subst.
rewrite PTree.gss in H3. inv H3.
rewrite Map.gss.
eexists; split; eauto.
rewrite Map.gso by auto.
apply (H id ty).
rewrite PTree.gso in H3 by auto.
simpl. auto.
Qed.

Lemma later_exp'' (A: Type) (ND: NatDed A)(Indir: Indir A):
      forall T : Type,
       (exists x: T, True) ->
       forall F : T -> A,
       |> (EX x : _, F x) = EX x : T, |> F x.
Proof.
intros.
destruct H as [x _].
apply later_exp'; auto.
Qed.

Lemma semax_call_subsume:
  forall (fs1: funspec) A P Q NEP NEQ argsig retsig cc,
    subsume_funspec fs1 (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)  ->
   forall {CS: compspecs} {Espec: OracleKind} Delta  ts x (F: environ -> mpred) ret  a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->   
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         (`(func_ptr fs1) (eval_expr a) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof.
intros until cc. intro H2; intros.
destruct fs1.
destruct H2 as [? [? ?]].
subst c f.
specialize (H4 ts x).
apply semax_pre with
  (|> (tc_expr Delta a && tc_exprlist Delta (snd (split argsig)) bl) &&
   ((` (func_ptr (mk_funspec (argsig, retsig) cc A0 P0 Q0 P_ne Q_ne)))
      (eval_expr a) &&
     |> (F *
          (EX ts1:list Type, EX x1:(functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts1 A0) mpred), EX F':mpred,  
            !! (ENTAIL ret0_tycon
                      (funsig_tycontext
                         (funsig_of_funspec
                            (mk_funspec (argsig, retsig) cc A0 P0 Q0 P_ne Q_ne))), `F' * Q0 ts1 x1 |-- Q ts x) && 
          (@liftx (Tarrow environ (LiftEnviron mpred))  (`F' * P0 ts1 x1)
          (make_args' (argsig, retsig)
             (eval_exprlist (snd (split argsig)) bl))))))).
-
set (fp := ` (func_ptr (mk_funspec (argsig, retsig) cc A0 P0 Q0 P_ne Q_ne))) in *.
intro rho.
unfold local, lift1.
simpl.
apply derives_extract_prop; intro.
apply andp_right; [ apply andp_left1; auto | ].
apply andp_right; [ apply andp_left2; apply andp_left1; auto | ].
rewrite andp_comm.
rewrite andp_assoc.
apply andp_left2.
rewrite <- later_andp.
apply later_derives.
unfold_lift.
simpl funsig_of_funspec in H4.
specialize (H4 (make_args' (argsig, retsig) (eval_exprlist (snd (split argsig)) bl)
     rho)).
unfold local, lift1 in H4. simpl in H4.
simpl.
apply derives_trans with
  (!! (tc_environ (funsig_tycontext (argsig, retsig))
          (make_args' (argsig, retsig)
             (eval_exprlist (snd (split argsig)) bl) rho)) &&
    (F rho *
    P ts x
     (make_args' (argsig, retsig) (eval_exprlist (snd (split argsig)) bl)
        rho))).
rewrite andp_comm.
apply andp_derives.
apply andp_left2; apply tc_environ_make_args'; auto.
apply derives_refl.
apply derives_extract_prop; intro.
apply sepcon_derives; auto.
rewrite (prop_true_andp (tc_environ _ _)) in H4 by auto.
eapply derives_trans. apply H4.
Intros ts1 x1 F'. Exists ts1 x1 F'.
rewrite prop_true_andp by auto.
apply derives_refl.
-
rewrite (andp_comm (|> _)).
rewrite andp_assoc.
rewrite <- later_andp.
rewrite exp_sepcon2, exp_andp1.
apply extract_exists_pre_later; intro ts1.
rewrite exp_sepcon2, exp_andp1.
apply extract_exists_pre_later; intro x1.
rewrite exp_sepcon2, exp_andp1.
apply extract_exists_pre_later; intro F'.
apply semax_pre with
  (|> !! (ENTAIL ret0_tycon
                      (funsig_tycontext
                         (funsig_of_funspec
                            (mk_funspec (argsig, retsig) cc A0 P0 Q0
                               P_ne Q_ne))), `F' * Q0 ts1 x1 |-- 
             Q ts x) &&
   ( |> (tc_expr Delta a && tc_exprlist Delta (snd (split argsig)) bl) &&
   ((` (func_ptr (mk_funspec (argsig, retsig) cc A0 P0 Q0 P_ne Q_ne)))
      (eval_expr a) &&
    (|> F *
     |> (@liftx (Tarrow environ (LiftEnviron mpred)) (`F' * P0 ts1 x1))
           (make_args' (argsig, retsig)
              (eval_exprlist (snd (split argsig)) bl)))))).
apply andp_left2.
rewrite !later_andp.
apply andp_right.
apply andp_left2. apply andp_left1.
apply later_derives.
normalize.
apply andp_right.
apply andp_left2.
apply andp_left2; auto.
apply derives_refl.
apply andp_right.
apply andp_left1; auto.
apply andp_left2.
apply andp_left1.
rewrite <- later_sepcon.
apply later_derives.
normalize.
apply derives_refl.
apply semax_extract_later_prop; intro.
eapply semax_pre_post'; [ | | apply semax_call; eauto; clear -H0; intuition].
*
apply andp_left2.
apply andp_derives; auto.
apply andp_derives.
apply derives_refl.
simpl in F'.
rewrite <- later_sepcon.
apply later_derives.
apply derives_trans with
((F * `F')
      * @liftx (Tarrow environ (LiftEnviron mpred)) (P0 ts1 x1)
     (make_args' (argsig, retsig) (eval_exprlist (snd (split argsig)) bl))).
intro rho; unfold_lift. simpl. rewrite <- sepcon_assoc. apply derives_refl.
apply derives_refl.
*
clear H4.
simpl ret0_tycon in H2.
Intros old. Exists old.
forget (Q0 ts1 x1) as QQ0.
forget (Q ts x) as QQ.
clear x x1.
change
  (functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts (rmaps.ArrowType (rmaps.ConstType environ)
             rmaps.Mpred)) mpred) in QQ, QQ0.
apply ENTAIL_trans with
 (substopt ret (` old) F *
  (`F' * maybe_retval QQ0 retsig ret)). 
{
 apply andp_left2.
 intro rho; unfold substopt, subst; unfold_lift; destruct ret; simpl;
 rewrite <- sepcon_assoc; auto.
}
intro rho; simpl.
unfold_lift.
unfold local, lift1.
apply derives_extract_prop; intro H8.
apply sepcon_derives; auto.
unfold SeparationLogic.maybe_retval, maybe_retval.
change (functors.MixVariantFunctor._functor
   (rmaps.dependent_type_functor_rec ts (rmaps.ArrowType (rmaps.ConstType environ) rmaps.Mpred)) mpred)
  in QQ, QQ0.
destruct ret; [ | destruct (eq_dec retsig Tvoid)] .
+
eapply derives_trans; [ | apply H2].
unfold local, lift1.
simpl.
rewrite prop_true_andp; auto.
unfold_lift; auto.
split3.
--
clear QQ QQ0 H2.
hnf; intros.
unfold ret0_tycon, temp_types in H2.
rewrite PTree.gempty in H2; inv H2.
(*  ALL THIS STUFF WOULD BE USEFUL if we used ret_tycon instead
     of ret0_tycon . . .
simpl ret_type in H2.
assert (is_void_type retsig = false).
  clear - H0. destruct retsig; try reflexivity.
   try match type of H0 with _ <-> _ => destruct H0 as [H0 _] end.
   specialize (H0 (eq_refl _)); inv H0.
rewrite H3 in H2.
destruct (ident_eq id ret_temp).
2: rewrite PTree.gso in H2 by auto; rewrite PTree.gempty in H2; inv H2.
subst id.
rewrite PTree.gss in H2. inv H2.
simpl.
unfold Map.get, Map.set.
rewrite if_true by auto.
clear - H1 H8.
hnf in H1.
destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
subst.
destruct H8 as [? _].
specialize (H i t Heqo).
destruct H as [v [? ?]]; exists v; split; auto.
unfold Map.get, te_of in H.
destruct rho. unfold eval_id. simpl. unfold Map.get. rewrite H.  reflexivity.
*)
--
clear.
hnf; intros.
simpl. rewrite PTree.gempty. split; intro. inv H.
destruct H. inv H.
--
clear.
hnf; intros.
simpl in *. rewrite PTree.gempty in H. inv H.
+
subst retsig.
eapply derives_trans; [ | apply H2].
unfold local, lift1.
simpl.
rewrite prop_true_andp; auto.
unfold_lift; auto.
split3.
--
clear QQ QQ0 H2.
hnf; intros.
unfold ret0_tycon, temp_types in H2.
simpl ret_type in H2.
simpl in H2. rewrite PTree.gempty  in H2. inv H2.
--
clear.
hnf; intros.
simpl. rewrite PTree.gempty. split; intro. inv H.
destruct H. inv H.
--
clear.
hnf; intros.
simpl in *. rewrite PTree.gempty in H. inv H.
+
(* rewrite (proj2 H0) in n. contradiction n; auto. auto. *)
assert (@derives mpred _
             (F' * EX v : val, QQ0 (make_args (ret_temp :: nil) (v :: nil) rho))
             (EX v : val, QQ (make_args (ret_temp :: nil) (v :: nil) rho))).
2: destruct retsig; [contradiction n; auto | assumption.. ].
Intros v. Exists v.
specialize (H2 (make_args (ret_temp :: nil) 
     (v :: nil) rho)).
simpl in H2.
simpl.
eapply derives_trans; [ | apply H2].
unfold_lift; unfold local, lift1; simpl.
apply andp_right; auto.
apply prop_right.
unfold ret0_tycon.
split3.
--
unfold temp_types.
intros id ty ?.
rewrite PTree.gempty in H3; inv H3.
--
clear.
hnf; intros.
simpl. rewrite PTree.gempty. split; intro. inv H.
destruct H. inv H.
--
clear.
hnf; intros.
simpl in *. rewrite PTree.gempty in H. inv H.
Qed.

Lemma semax_call_NDsubsume :
  forall (fs1: funspec) A P Q argsig retsig cc,
    NDsubsume_funspec fs1 
        (NDmk_funspec  (argsig,retsig) cc A P Q)  ->
     forall {CS: compspecs} {Espec: OracleKind},
    forall  Delta  x (F: environ -> mpred) ret a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         (`(func_ptr fs1) (eval_expr a) &&
          |>(F * `(P x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q x) retsig ret)).
Proof.
intros.
apply (semax_call_subsume fs1 (rmaps.ConstType A) (fun _ => P) (fun _ => Q)
   (const_super_non_expansive A _) (const_super_non_expansive A _)
    argsig retsig cc); auto.
clear - H.
destruct fs1.
destruct A0; try contradiction.
destruct H as [? [? ?]].
subst f c.
split3; auto.
intros.
Exists (@nil Type).
auto.
apply nil.
Qed.

Module Junk.   (* experiments, not necessarily useful *)

Definition subsume_funspec0 (f1 f2 : funspec) :=
 match f1 with
 | mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
   fsig1 = fsig2 /\ cc1 = cc2 /\
     forall ts2 x2,
     exists ts1 x1, 
           P2 ts2 x2 |-- P1 ts1 x1 /\
           Q1 ts1 x1 |-- Q2 ts2 x2
  end end.

Definition subsume_funspec' (f1 f2 : funspec) :=
 match f1 with
 | mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
   fsig1 = fsig2 /\ cc1 = cc2 /\
     forall ts2 x2, exists ts1, 
        P2 ts2 x2 |-- EX x1:_, 
                             ((P1 ts1 x1) &&
                             (!! (Q1 ts1 x1 |-- Q2 ts2 x2)))
  end end.

Lemma subsume_semax_body: 
  forall fs1 fs2 (H: subsume_funspec0 fs1 fs2),
   forall Vprog Gprog cs f id,
    @semax_body Vprog Gprog cs f (id,fs1) ->
    @semax_body Vprog Gprog cs f (id,fs2).
Proof.
intros.
destruct fs2 as [fsig2 cc2 A2 P2 Q2 HP2 HQ2].
destruct fs1 as [fsig1 cc1 A1 P1 Q1 HP1 HQ1].
destruct H as [? [? ?]].
subst fsig2 cc2.
red in H0|-*.
intros. specialize (H0 Espec).
specialize (H2 ts x).
destruct H2 as [ts2 [x2 [H2 H2']]].
eapply semax_pre_post; [ .. | apply H0].
clear H0.
apply andp_left2.
apply sepcon_derives; auto.
apply H2.
all: try solve [apply andp_left2; intro; simpl; auto].
intros.
apply andp_left2.
simpl.
intros.
apply sepcon_derives; auto.
unfold bind_ret.
destruct vl.
simpl.
apply andp_derives; auto.
unfold_lift.
apply H2'.
destruct (fn_return f); auto.
unfold_lift.
apply H2'.
Qed.

Lemma subsume_semax_body': 
  forall fs1 fs2 (H: subsume_funspec' fs1 fs2),
   forall Vprog Gprog cs f id,
    @semax_body Vprog Gprog cs f (id,fs1) ->
    @semax_body Vprog Gprog cs f (id,fs2).
Proof.
intros.
destruct fs2 as [fsig2 cc2 A2 P2 Q2 HP2 HQ2].
destruct fs1 as [fsig1 cc1 A1 P1 Q1 HP1 HQ1].
destruct H as [? [? ?]].
subst fsig2 cc2.
red in H0|-*.
intros. specialize (H0 Espec).
specialize (H2 ts x).
destruct H2 as [ts2 H2].
specialize (H0 ts2).
eapply semax_pre.
apply andp_left2.
apply sepcon_derives; [ | apply derives_refl].
apply H2.
Intros x1.
normalize.
apply semax_extract_prop; intro.
specialize (H0 x1).
eapply semax_post; [  .. | apply H0].
all: try solve [apply andp_left2; intro; simpl; auto].
intros.
apply andp_left2.
simpl.
intros.
apply sepcon_derives; auto.
unfold bind_ret.
destruct vl.
simpl.
apply andp_derives; auto.
unfold_lift.
auto.
destruct (fn_return f); auto.
unfold_lift.
auto.
Qed.

Definition subsume_funspec'' (Delta: tycontext) (f1 f2 : funspec) :=
 match f1 with
 | mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
   fsig1 = fsig2 /\ cc1 = cc2 /\
     forall ts2 x2, exists ts1, 
        ENTAIL Delta, P2 ts2 x2 |-- EX x1:_, 
                             ((P1 ts1 x1) &&
                             (!! (ENTAIL (ret_tycon Delta), Q1 ts1 x1 |-- Q2 ts2 x2)))
  end end.

Import ListNotations.

Lemma subsume_semax_body'': 
   forall Vprog Gprog cs f id fs1 fs2,
    subsume_funspec'' (func_tycontext f Vprog Gprog nil) fs1 fs2 ->
    @semax_body Vprog Gprog cs f (id,fs1) ->
    @semax_body Vprog Gprog cs f (id,fs2).
Proof.
intros.
destruct fs2 as [fsig2 cc2 A2 P2 Q2 HP2 HQ2].
destruct fs1 as [fsig1 cc1 A1 P1 Q1 HP1 HQ1].
destruct H as [? [? ?]].
subst fsig2 cc2.
red in H0|-*.
intros. specialize (H0 Espec).
specialize (H2 ts x).
destruct H2 as [ts2 H2].
specialize (H0 ts2).
eapply semax_pre.
apply derives_trans with
 (sepcon  (andp (local (tc_environ (func_tycontext f Vprog Gprog nil)))
     (P2 ts x)) (stackframe_of f)).
intro rho. unfold local, lift1. simpl. normalize.
apply sepcon_derives; [ | apply derives_refl].
apply H2.
Intros x1.
normalize.
apply semax_extract_prop; intro.
specialize (H0 x1).
eapply semax_post; [  .. | apply H0].
all: try solve [apply andp_left2; intro; simpl; auto].
intros.
intro rho.
simpl.
apply derives_trans with
 ((local (tc_environ (func_tycontext f Vprog Gprog nil)) rho &&
   bind_ret vl (fn_return f) (Q1 ts2 x1) rho) * stackframe_of f rho).
unfold local, lift1. normalize.
apply sepcon_derives; auto.
unfold bind_ret.
unfold local, lift1.
normalize.
destruct vl.
*
clear - H H1.
simpl.
apply derives_extract_prop; intro.
rewrite prop_true_andp by auto.
pose proof (make_args1_tc_environ rho (func_tycontext f Vprog Gprog [])
                       v H1 H0).
replace (ret1_tycon (func_tycontext f Vprog Gprog nil))
   with (ret_tycon (func_tycontext f Vprog Gprog nil)) in H2.
specialize (H (make_args [ret_temp] [v] rho)).
unfold local, lift1 in H.
simpl in H.
rewrite prop_true_andp in H by auto.
apply H.
unfold ret_tycon, ret1_tycon.
simpl.
replace (is_void_type (fn_return f)) with false; auto.
clear - H0.
destruct (fn_return f); destruct v; try contradiction; auto.
*
destruct (fn_return f) eqn:?; auto.
unfold_lift.
pose proof (make_args0_tc_environ rho (func_tycontext f Vprog Gprog nil)
                       H1).
replace (ret0_tycon (func_tycontext f Vprog Gprog nil))
   with (ret_tycon (func_tycontext f Vprog Gprog nil)) in H3.
specialize (H (make_args nil nil rho)).
unfold local, lift1 in H.
simpl in H.
rewrite prop_true_andp in H by auto.
apply H.
unfold ret0_tycon, ret_tycon.
simpl.
rewrite Heqt.
reflexivity.
Qed.

Lemma tycontext_sub6:
  forall Vprog Gprog f rho, 
      tc_environ (make_tycontext (fn_params f) (fn_temps f) (fn_vars f) 
         (fn_return f) Vprog Gprog nil) rho ->
      tc_environ (make_tycontext (fn_params f) nil nil (fn_return f) nil nil nil) rho.
Proof.
intros.
destruct H as [? [? ?]].
split3.
*
forget (fn_params f) as al.
forget (fn_temps f) as bl.
clear - H.
simpl in *.
intros id ty H0; specialize (H id ty).
spec H; auto.
clear - H0.
induction al.
+ simpl in *. rewrite PTree.gempty in H0. inv H0.
+ simpl in *.
    destruct (ident_eq (fst a) id). 
    rewrite e in *; auto. rewrite !PTree.gss in *. auto.
    rewrite !PTree.gso by auto. apply IHal.
    rewrite PTree.gso in H0 by auto. auto.
*
clear - H0 H1.
hnf; intros.
hnf in H0. specialize (H0 id ty).
simpl in H0.
simpl.
rewrite <- H0. clear H0.
rewrite PTree.gempty.
admit.  (* not true *)
*
hnf; intros.
simpl in H2.
rewrite PTree.gempty in H2. inv H2.
all: fail.
Abort.

Lemma tycontext_sub_i6:
  forall Vprog Gprog f, 
  tycontext_sub (make_tycontext (fn_params f) nil nil (fn_return f) nil nil nil)
     (make_tycontext (fn_params f) (fn_temps f) (fn_vars f) 
         (fn_return f) Vprog Gprog nil).
Proof.
intros.
split3; [ | | split3]; simpl; intros; auto.
*
destruct ((make_tycontext_t (fn_params f) nil) ! id) eqn:?H; auto.
replace ((make_tycontext_t (fn_params f) (fn_temps f)) ! id)
  with ((make_tycontext_t (fn_params f) nil) ! id).
rewrite H; auto.
forget (fn_params f) as al.
forget (fn_temps f) as bl.
induction al.
+ simpl in *. rewrite PTree.gempty in H. inv H.
+ simpl in *.
    destruct (ident_eq (fst a) id). 
    rewrite e. rewrite !PTree.gss. auto.
    rewrite !PTree.gso by auto. apply IHal.
    rewrite PTree.gso in H by auto. auto.
*
Locate denote_tc_lvar.
admit.  (* not true *)
*
hnf.
rewrite PTree.gempty. auto.
*
split.
intros. hnf. rewrite PTree.gempty. auto.
intros.
rewrite !PTree.gempty. constructor.
all:fail.
Abort.

Lemma subsume_semax_body3: 
   forall Vprog Gprog cs f id fs1 fs2,
    funsig_of_function f = funsig_of_funspec fs2 ->
    subsume_funspec'' (funsig_tycontext (funsig_of_funspec fs2)) fs1 fs2 ->
    @semax_body Vprog Gprog cs f (id,fs1) ->
    @semax_body Vprog Gprog cs f (id,fs2).
Proof.
intros until fs2. intros Hsig. intros.
(*
assert (Hsub:
  forall rho, tc_environ (func_tycontext f Vprog Gprog nil) rho  ->
      tc_environ (funsig_tycontext (funsig_of_funspec fs2)) rho). {
intro.
rewrite <- Hsig.
unfold func_tycontext.
unfold funsig_of_function; simpl.
unfold tc_environ.
apply semax_lemmas.typecheck_environ_sub.
apply tycontext_sub_i6; auto.
}
*)
destruct fs2 as [fsig2 cc2 A2 P2 Q2 HP2 HQ2].
destruct fs1 as [fsig1 cc1 A1 P1 Q1 HP1 HQ1].
destruct H as [? [? ?]].
subst fsig2 cc2.
red in H0|-*.
intros. specialize (H0 Espec).
specialize (H2 ts x).
destruct H2 as [ts2 H2].
specialize (H0 ts2).
eapply semax_pre.
apply derives_trans with
 (sepcon  (andp (local (tc_environ (func_tycontext f Vprog Gprog nil)))
     (P2 ts x)) (stackframe_of f)).
intro rho. unfold local, lift1. simpl. normalize.
apply sepcon_derives; [ | apply derives_refl].
eapply derives_trans; [ | apply H2]. 
{
simpl funsig_tycontext.
apply andp_right; auto.
apply andp_left1.
clear - Hsig.
simpl in Hsig. subst fsig1.
clear.
Print typecheck_environ.
admit.
apply ENTAIL_refl.
}
Intros x1.
normalize.
apply semax_extract_prop; intro.
specialize (H0 x1).
eapply semax_post; [  .. | apply H0].
all: try solve [apply andp_left2; intro; simpl; auto].
intros.
intro rho.
simpl.
apply derives_trans with
 ((local (tc_environ (func_tycontext f Vprog Gprog nil)) rho &&
   bind_ret vl (fn_return f) (Q1 ts2 x1) rho) * stackframe_of f rho).
unfold local, lift1. normalize.
apply sepcon_derives; auto.
unfold bind_ret.
normalize.
simpl funsig_of_funspec in *.
apply derives_extract_prop; intro.
assert (H7: fn_return f = snd fsig1). 
  { clear - Hsig. unfold funsig_of_funspec, funsig_of_function in Hsig.
    rewrite <- Hsig. reflexivity.
}
destruct vl.
*
clear - H H1 H7.
simpl.
apply derives_extract_prop; intro.
rewrite prop_true_andp by auto.
generalize H0; intro H0'.
rewrite H7 in H0'.
unfold_lift.
eapply derives_trans; [ | apply H].
unfold ret_tycon.
simpl ret_type.
rewrite <- H7.
assert (is_void_type (fn_return f) = false). {
  clear - H0. hnf in H0. destruct (fn_return f); try reflexivity. contradiction.
}
rewrite H2.
match goal with |- context [local ?A] => set (aa:=A) end.
unfold local, lift1; simpl.
rewrite prop_true_andp; auto.
subst aa.
clear - H1 H0.
split3; hnf; intros.
unfold temp_types in *.
destruct (ident_eq ret_temp id).
subst.
rewrite PTree.gss in H.
inv H. exists v.
simpl. rewrite Map.gss. split; auto. apply tc_val_tc_val'; auto.
rewrite PTree.gso in * by auto.
rewrite PTree.gempty in H; inv H.
unfold var_types.
rewrite PTree.gempty.
split; intros. inv  H.
destruct H.
simpl in H. unfold Map.get, Map.empty in H. inv H.
unfold glob_types in H.
destruct fsig1; simpl in H.
rewrite PTree.gempty in H. inv H.

*
destruct (fn_return f) eqn:?; auto.
unfold_lift.
eapply derives_trans; [ | apply H].
match goal with |- context [local ?A] => set (aa:=A) end.
unfold local, lift1; simpl.
rewrite prop_true_andp; auto.
subst aa.
hnf.
split3; hnf; intros.
+
unfold typecheck_temp_environ.
simpl in H3; rewrite <- H7 in H3. simpl in H3. rewrite PTree.gempty in H3. inv H3.
+
simpl.
rewrite PTree.gempty.
unfold Map.get, Map.empty.
clear; split; intros. inv H. destruct H. inv H.
+
simpl in H3. rewrite PTree.gempty in H3. inv H3.
all:fail.
Abort.

End Junk.
