Require Import mc_reify.func_defs.
Require Import mc_reify.list_ctype_eq.
Require Import mc_reify.get_set_reif.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.RTac.Core.
(*Require Import MirrorCharge.RTac.ReifyLemma.*)
Require Import mc_reify.update_tycon.
Require Import mc_reify.set_reif.
Require Import mc_reify.nth_reif.
Require Import mc_reify.solve_exprD.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.ExprDsimul.
Require Import get_set_reif_soundness.
Import ExprDenote.


Section tbled.

Existing Instance SubstUpdate_ctx_subst.

Variable tbl : SymEnv.functions RType_typ.

Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Existing Instance SubstOk_ctx_subst.
Existing Instance SubstUpdate_ctx_subst.
Existing Instance SubstUpdateOk_ctx_subst.
Existing Instance RType_typ.
Existing Instance Typ2_tyArr.
Existing Instance Expr_expr.
Existing Instance MA.
Existing Instance Expr_ok_fs.
Instance MentionsAnyOk : MentionsAnyOk MA _ _.
Admitted.

Ltac solve_exprD := solve_exprD.solve_exprD tbl.
Opaque type_cast.


Definition AFTER_SET_LOAD : rtac typ (expr typ func) :=
fun tus tvs n m c s e =>
  match e with
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match l with
  | App
      (App (App (Inj (inr (Smx fassertD))) P)
         (App
            (App (Inj (inr (Smx flocalD)))
               (App
                  (App (Inj (inr (Data (fset tyval id))))
                     v) T1)) T2)) R =>
    let l' :=
    App
      (App (App (Inj (inr (Smx fassertD))) P)
         (App
            (App (Inj (inr (Smx flocalD)))
                  (set_reif id v T1 tyval)) T2)) R
    in
    match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l' r ty s with
    | Some s => RTac.Core.Solved s
    | None =>  RTac.Core.Fail
    end
  | _ => RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Lemma AFTER_SET_LOAD_sound : rtac_sound AFTER_SET_LOAD.
Proof.
unfold rtac_sound.
intros.
unfold AFTER_SET_LOAD in *.
repeat (destruct_match H; try solve [subst; apply rtac_spec_Fail]; try congruence).
pose proof (exprUnify_sound).
specialize (H0 (ctx_subst ctx) typ func  _ _ _ _ _ _ _ _

_ _ 3).
subst.
red in H0. red in H0.
unfold rtac_spec. simpl. intros.
apply H0 with (tv' := nil) in Heqo1; auto. clear H0.
destruct Heqo1.

split. auto.
forward. simpl in *.
unfold propD in H4. unfold exprD'_typ0 in H4.
simpl in H4.
solve_exprD.
unfold exprT_App. simpl.
destruct (pctxD_substD H1 H3).
destruct H4.
edestruct (H2 ( (fun (us0 : HList.hlist types.typD (getUVars ctx))
             (vs0 : HList.hlist types.typD (getVars ctx)) =>
           local2ptree.assertD (e14 us0 vs0)
             (local2ptree.localD
                (Maps.PTree.set p (e13 us0 vs0) (e11 us0 vs0))
                (e8 us0 vs0)) (e5 us0 vs0)))); eauto.

solve_exprD.
edestruct set_reif_exprD. apply Heqo14.
eauto.
instantiate (1 := p) in H6.
pose_types tbl. fold func in *. unfold RSym_sym in *.
 progress_match. solve_funcAs.
solve_exprD. unfold exprT_App. simpl.
erewrite <- set_reif_eq2 in H6; eauto.
solve_exprD.
forward_reason.
destruct (substD_pctxD _ H0 H3 H6).
forward_reason.
forward. inv_some.
split. admit. (*what is this*)
intros.  gather_facts.
eapply Pure_pctxD. eauto.
intros. simpl in *.
edestruct H7; eauto.
specialize (H11 HList.Hnil).
apply H11.
Admitted.

Definition AFTER_STORE : rtac typ (expr typ func) :=
fun tus tvs n m c s e =>
  match e with
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match l with
  | App
      (App (App (Inj (inr (Smx fassertD))) P) Q)
      (App
         (App (Inj (inr (Data (freplace_nth tympred n)))) R) Rn) =>
    let l' :=
    App
      (App (App (Inj (inr (Smx fassertD))) P) Q)
      (rreplace_nth tympred n R Rn)
    in
    match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l' r ty s with
    | Some s => RTac.Core.Solved s
    | None =>  RTac.Core.Fail
    end
  | _ => RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Lemma AFTER_STORE_sound : rtac_sound AFTER_STORE.
Proof.
unfold rtac_sound.
intros.
unfold AFTER_STORE in *.
repeat (destruct_match H; try solve [subst; apply rtac_spec_Fail]; try congruence).
pose proof (exprUnify_sound).
specialize (H0 (ctx_subst ctx) typ func  _ _ _ _ _ _ _ _

_ _ 3).
subst.
red in H0. red in H0.
unfold rtac_spec. simpl. intros.
apply H0 with (tv' := nil) in Heqo1; auto. clear H0.
destruct Heqo1.

split. auto.
forward. simpl in *.
unfold propD in H4. unfold exprD'_typ0 in H4.
simpl in H4.
solve_exprD.
unfold exprT_App. simpl.
destruct (pctxD_substD H1 H3).
destruct H4.
edestruct (H2 ( (fun (us0 : HList.hlist types.typD (getUVars ctx))
             (vs0 : HList.hlist types.typD (getVars ctx)) =>
           local2ptree.assertD (e11 us0 vs0) (e9 us0 vs0)
             (canon.replace_nth n (e7 us0 vs0) (e6 us0 vs0))))); eauto.
admit.
forward_reason.
destruct (substD_pctxD _ H0 H3 H6).
forward_reason.
forward. inv_some.
split. admit. (*what is this*)
intros.  gather_facts.
eapply Pure_pctxD. eauto.
intros. simpl in *.
edestruct H7; eauto.
specialize (H11 HList.Hnil).
apply H11.
Admitted.

Definition REFLEXIVITYTAC : rtac typ (expr typ func) :=
fun tus tvs n m c s e =>
  match e with
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l r ty s with
    | Some su => RTac.Core.Solved su
    | None =>  RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Lemma REFLEXIVITYTAC_sound  :
rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) REFLEXIVITYTAC.
unfold rtac_sound.
intros.
unfold REFLEXIVITYTAC in H.
do 7 (match type of H with
          | match ?g with _ => _ end = _ => destruct g eqn:?;
                      try solve [simpl in H; subst;
                      try apply rtac_spec_Fail]
        end).
pose proof (exprUnify_sound).
specialize (H0 (ctx_subst ctx) typ func  _ _ _ _ _ _ _ _

_ _ 3).
subst.
red in H0. red in H0.
unfold rtac_spec. simpl. intros.
apply H0 with (tv' := nil) in Heqo1; auto. clear H0.
destruct Heqo1.

split. auto.
forward. simpl in *.
unfold propD in H4. unfold exprD'_typ0 in H4.
simpl in H4.

solve_exprD.
unfold exprT_App. simpl.
destruct (pctxD_substD H1 H3).
destruct H4.
edestruct H2; eauto.
forward_reason.
destruct (substD_pctxD _ H0 H3 H6).
forward_reason.
forward. inv_some.
split. admit. (*what is this*)
intros.  gather_facts.
eapply Pure_pctxD. eauto.
intros. simpl in *.
edestruct H7; eauto.
specialize (H11 HList.Hnil).
apply H11.
Admitted.

Definition REFLEXIVITY := REFLEXIVITYTAC.


Definition REFLEXIVITYTAC_msubst : rtac typ (expr typ func) :=
fun tus tvs n m c s e =>
  match e with
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match l with
  | App
      (App
         (App
            (App (Inj (inr (Smx fmsubst_eval_LR))) T1) T2)
         (Inj (inr (Const (fCexpr e1)))))
      (Inj (inr (Const (fllrr lr)))) =>
    let l' := rmsubst_eval_LR T1 T2 e1 lr in
    match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l' r ty s with
    | Some s => RTac.Core.Solved s
    | None =>  RTac.Core.Fail
    end
  | _ => RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Definition REFLEXIVITY_MSUBST := REFLEXIVITYTAC_msubst.

Definition REFLEXIVITYTAC_msubst_efield : rtac typ (expr typ func) :=
fun tus tvs n m c s e =>
  match e with
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match l with
  | App (App (Inj (inr (Smx (fmsubst_efield_denote e)))) T1) T2 =>
    let l' := rmsubst_efield_denote T1 T2 e in
    match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l' r ty s with
    | Some s => RTac.Core.Solved s
    | None =>  RTac.Core.Fail
    end
  | _ => RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Definition REFLEXIVITY_MSUBST_EFIELD := REFLEXIVITYTAC_msubst_efield.

Definition REFLEXIVITYTAC_nth_error : rtac typ (expr typ func) :=
fun tus tvs n m c s e =>
  match e with
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match l with
  | App (Inj (inr (Data (fnth_error ty n)))) xs =>
    let l' := rnth_error ty xs n in
    match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l' r ty s with
    | Some s => RTac.Core.Solved s
    | None =>  RTac.Core.Fail
    end
  | _ => RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Definition REFLEXIVITY_NTH_ERROR := REFLEXIVITYTAC_nth_error.

Definition REFLEXIVITY_DENOTE (rtype : typ) {H: @RelDec.RelDec (typD rtype) eq}
{H0: RelDec.RelDec_Correct H} tbl : rtac typ (expr typ func) :=
   fun tus tvs lus lvs c s e => (
match e with
| (App (App (Inj (inr (Other (feq _)))) l) r) =>
  match func_defs.reflect tbl nil nil l rtype, func_defs.reflect tbl nil nil r rtype with
  | Some v1, Some v2 => if @RelDec.rel_dec _ eq H v1 v2 then Solved s else Fail
  | _, _ => Fail
  end
| _ => Fail
end).

Lemma REFLEXIVITY_DENOTE_sound (rtype : typ) {H: @RelDec.RelDec (typD rtype) eq}
{H0: RelDec.RelDec_Correct H}:
rtac_sound (REFLEXIVITY_DENOTE rtype tbl).
unfold rtac_sound.
intros.
unfold REFLEXIVITY_DENOTE in H1.
repeat (match type of H1 with
          | match ?g with _ => _ end = _ => destruct g eqn:?;
                      try solve [simpl in H; subst;
                      try apply rtac_spec_Fail]
        end).
subst. simpl. intros.
split.
unfold func_defs.reflect, exprD in *. simpl in *.
solve_exprD.
forward. split. reflexivity.
intros.
unfold propD, exprD'_typ0 in *.  simpl in H4.
solve_exprD.
unfold exprT_App. simpl.
eapply Pure_pctxD. eauto.
intros.
unfold func_defs.reflect, exprD in *. simpl in *.
forward. inv_some.
inversion H0. rewrite rel_dec_correct in Heqb.
generalize (ExprFacts.exprD'_weaken    _ _ _ (getUVars ctx) (getVars ctx)  H4).
generalize (ExprFacts.exprD'_weaken    _ _ _ (getUVars ctx) (getVars ctx)  H5).
intros.
destruct H6, H7. simpl  in *. destruct H6, H7.
fold func in *. unfold RSym_sym in *.
solve_exprD.
specialize (H8 HList.Hnil HList.Hnil).
specialize (H9 HList.Hnil HList.Hnil).
simpl in *.
solve_exprD.
Qed.

Definition REFLEXIVITY_BOOL := REFLEXIVITY_DENOTE tybool.

Definition REFLEXIVITY_BOOL_sound := REFLEXIVITY_DENOTE_sound tybool.

Definition REFLEXIVITY_CEXPR := REFLEXIVITY_DENOTE tyc_expr.

Definition REFLEXIVITY_CEXPR_sound := REFLEXIVITY_DENOTE_sound tyc_expr.

Definition REFLEXIVITY_CTYPE := REFLEXIVITY_DENOTE (tyc_type).

Definition REFLEXIVITY_CTYPE_sound := REFLEXIVITY_DENOTE_sound (tyc_type).

Instance RelDec_op_ctypes_beq : @RelDec.RelDec (option Ctypes.type) eq :=
  Option.RelDec_eq_option RelDec_ctype_beq.

Instance RelDec_Correct_op_ctypes_beq : RelDec.RelDec_Correct RelDec_op_ctypes_beq :=
  Option.RelDec_Correct_eq_option RelDec_Correct_ctype_beq.

Definition REFLEXIVITY_OP_CTYPE := REFLEXIVITY_DENOTE (tyoption tyc_type).

Definition REFLEXIVITY_OP_CTYPE_sound := REFLEXIVITY_DENOTE_sound (tyoption tyc_type).


End tbled.
