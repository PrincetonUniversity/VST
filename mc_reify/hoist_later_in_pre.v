Require Import VST.floyd.proofauto.
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Require Export mc_reify.reify.
Require Export mc_reify.bool_funcs.
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
Require Import mc_reify.reified_ltac_lemmas.

(************************************************

Lemmas for rtac version of hoist_later_in_pre

************************************************)

Fixpoint rstrip_1_later_sep (R: expr typ func) : expr typ func :=
  match R with
  | Inj (inr (Data (fnil tympred))) => Inj (inr (Data (fnil tympred)))
  | App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
    match hd with
    | App (Inj (inr (Smx flater))) hd0 => App (App (Inj (inr (Data (fcons tympred)))) hd0) (rstrip_1_later_sep tl)
    | _ => App (App (Inj (inr (Data (fcons tympred)))) hd) (rstrip_1_later_sep tl)
    end
  | _ => R
  end.

Lemma SEPx_map_liftx: forall R, SEPx (map liftx R) = liftx (fold_right sepcon emp R).
Proof.
  intros.
  extensionality rho.
  unfold_lift; simpl.
  induction R.
  + reflexivity.
  + simpl.
    rewrite <- IHR.
    unfold SEPx.
    simpl.
    reflexivity.
Qed.

Lemma hoist_later_in_pre_aux:
    forall temp var ret gt s
      gs P T1 T2 R R' Post,
  forall {Espec: OracleKind},
      fold_right sepcon emp R |-- |> (fold_right sepcon emp R') ->
      semax (mk_tycontext temp var ret gt gs) (|> (assertD P (localD T1 T2) R')) s (normal_ret_assert Post) ->
      semax (mk_tycontext temp var ret gt gs) (assertD P (localD T1 T2) R) s (normal_ret_assert Post).
Proof.
  intros.
  eapply semax_pre0; [| exact H0].
  unfold assertD.
  apply PROP_later_derives.
  apply LOCAL_later_derives.
  rewrite !SEPx_map_liftx.
  intro.
  unfold_lift; simpl.
  exact H.
Qed.

Lemma fold_right_sepcon_later_derives: forall P P' Q Q' R,
  P |-- |> P' ->
  fold_right sepcon emp Q |-- |> (fold_right sepcon emp Q') ->
  (fold_right sepcon emp (P' :: Q')) = R ->
  fold_right sepcon emp (P :: Q) |-- |> R.
Proof.
  intros.
  subst.
  simpl.
  rewrite later_sepcon.
  apply sepcon_derives; auto.
Qed.

(************************************************

Reified Lemmas

************************************************)

Definition reify_hlip_base (temp : PTree.t (type * bool)) (var : PTree.t type)
         (ret : type) (gt : PTree.t type) (s : statement) : my_lemma.
reify_lemma reify_vst (hoist_later_in_pre_aux temp var ret gt s).
Defined.

(* Print reify_hlip_base. *)

Definition reify_hlip_ind : my_lemma.
reify_lemma reify_vst (fold_right_sepcon_later_derives).
Defined.

(* Print reify_hlip_ind. *)

Section tbled.

Variable tbl : SymEnv.functions RType_typ.
Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Definition solve_hd_in_hlip (hd: expr typ func) : rtac typ (expr typ func) :=
  match hd with
  | App (Inj (inr (Smx flater))) _ => EAPPLY typ func reify_derives_refl
  | _ => EAPPLY typ func reify_now_later
  end.

Fixpoint solve_strip_1_later (R: expr typ func) : rtac typ (expr typ func) :=
  match R with
  | Inj (inr (Data (fnil tympred))) => EAPPLY typ func reify_now_later
  | App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
    THEN (EAPPLY typ func reify_hlip_ind)
     (THEN (TRY (REFLEXIVITY tbl))
           (FIRST [solve_hd_in_hlip hd; solve_strip_1_later tl]))
  | _ => FAIL
  end.

Definition HLIP temp var ret gt R s :=
  THEN (EAPPLY typ func (reify_hlip_base temp var ret gt s))
       (TRY (solve_strip_1_later R)).

Let Expr_expr_fs := Expr_expr_fs tbl.
Existing Instance Expr_expr_fs.

Let Expr_ok_fs := Expr_ok_fs tbl.
Existing Instance Expr_ok_fs.

Let ExprVar_expr := @ExprVariables.ExprVar_expr typ func.
Existing Instance ExprVar_expr.

Existing Instance MA.

Existing Instance rtac_base.MentionsAnyOk.

Lemma HLIP_sound_aux0: forall temp var ret gt s, rtac_sound (EAPPLY typ func (reify_hlip_base temp var ret gt s)).
Proof.
  intros.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    unfold BILogicFunc.typ2_cast_bin in *. simpl in *.
    eapply hoist_later_in_pre_aux; eauto.
Qed.

Lemma HLIP_sound_aux1: rtac_sound (EAPPLY typ func reify_hlip_ind).
Proof.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    unfold BILogicFunc.typ2_cast_bin in *. simpl in *.
    eapply fold_right_sepcon_later_derives; eauto.
Qed.

Definition HLIP_sound_aux2 (hd: expr typ func): rtac_sound (solve_hd_in_hlip hd) :=
    match hd as hd'
      return rtac_sound match hd' with
                        | App (Inj (inr (Smx flater))) _ => EAPPLY typ func reify_derives_refl
                        | _ => EAPPLY typ func reify_now_later
                        end
    with
    | App (Inj (inr (Smx flater))) _ => APPLY_sound_derives_refl tbl
    | _ => APPLY_sound_now_later tbl
    end.

Print Forall_cons.
Lemma tttt: Forall (fun x => In x [1; 3; 4]) [1; 3; 4].
constructor; [| constructor; [| constructor; [| constructor]]].
+ left. reflexivity.
+ right. left. reflexivity.
+ right. right. left. reflexivity.
Qed.

Lemma solve_strip_1_later_def: forall R,
  match R with
  | Inj (inr (Data (fnil tympred))) => EAPPLY typ func reify_now_later
  | App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
    THEN (EAPPLY typ func reify_hlip_ind)
     (THEN (TRY (REFLEXIVITY tbl))
           (FIRST [solve_hd_in_hlip hd; solve_strip_1_later tl]))
  | _ => FAIL
  end =
  solve_strip_1_later R.
Proof.
  intros.
  repeat
  match goal with
  | [ |- context [match ?e with _ => _ end] ] => destruct e; auto
  end.
Qed. (* 5 seconds *)

Fixpoint solve_strip_1_later_sound (R: expr typ func) : rtac_sound (solve_strip_1_later R) :=
  let res :=
  match R as R'
    return rtac_sound match R' with
                      | Inj (inr (Data (fnil tympred))) => EAPPLY typ func reify_now_later
                      | App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
                        THEN (EAPPLY typ func reify_hlip_ind)
                         (THEN (TRY (REFLEXIVITY tbl))
                               (FIRST [solve_hd_in_hlip hd; solve_strip_1_later tl]))
                      | _ => FAIL
                      end
  with
  | Inj (inr (Data (fnil tympred))) => APPLY_sound_now_later tbl
  | App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
    THEN_sound tbl _ _ HLIP_sound_aux1
     (THEN_sound tbl _ _ (TRY_sound (REFLEXIVITYTAC_sound tbl))
                        (FIRST_sound (Forall_cons _ (HLIP_sound_aux2 hd)
                                       (Forall_cons _ (solve_strip_1_later_sound tl) (Forall_nil _)))))
  | _ => FAIL_sound
  end in
  eq_rect_r rtac_sound res (eq_sym (solve_strip_1_later_def R)). (*23 seconds *)

Lemma HLIP_sound: forall temp var ret gt R s, rtac_sound (HLIP temp var ret gt R s).
Proof.
  intros.
  unfold HLIP.
  apply THEN_sound.
  + apply HLIP_sound_aux0.
  + apply TRY_sound.
    apply solve_strip_1_later_sound.
Qed.

End tbled.
