Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.

Require Import VST.veric.seplog. (*For definition of tycontext*)

Import Cop.
Import Cop2.
Import Clight_Cop2.
Import Ctypes.

Section mpred.

Context `{!heapGS Σ}.

Lemma eval_lvalue_ptr : forall {CS: compspecs} rho e (Delta: tycontext) te ve ge,
mkEnviron ge ve te = rho ->
typecheck_var_environ ve (var_types Delta) ->
typecheck_glob_environ ge (glob_types Delta) ->
denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
⌜exists base, exists ofs, eval_lvalue e rho = Vptr base ofs⌝.
Proof.
intros.
induction e; eauto; simpl.
(*try now inversion H2.*)
* unfold typecheck_lvalue.
rewrite /get_var_type.
subst rho; simpl ve_of; simpl ge_of.
destruct_var_types i eqn:H4&?H; rewrite H4;
 [| destruct_glob_types i eqn:H6&?H; rewrite H6 ].
+ rewrite tc_bool_e; iPureIntro.
  exists b, Ptrofs.zero.
  simpl. by rewrite /eval_var H2 H.
+ rewrite tc_bool_e; iPureIntro.
  exists b, Ptrofs.zero.
  simpl. by rewrite /eval_var H3 H2.
+ iIntros "[]".
*
unfold typecheck_lvalue; fold typecheck_expr.
rewrite !denote_tc_assert_andp /=; unfold_lift.
iIntros "[_ %H4]".
destruct (eval_expr e rho); simpl; try now inversion H4; eauto.
*
unfold typecheck_lvalue; fold typecheck_lvalue.
rewrite denote_tc_assert_andp.
simpl in *. super_unfold_lift.
rewrite IHe; iIntros "[%IH H]".
unfold eval_field.
destruct IH as (base & ofs & IH).
destruct (eval_lvalue e rho); try congruence.
inv IH.
destruct (typeof e); try iDestruct "H" as "[]".
+
destruct (cenv_cs !! i0) as [co |]; [| iDestruct "H" as "[]"].
destruct (field_offset cenv_cs i (co_members co)); [| iDestruct "H" as "[]"].
destruct p. destruct b; [ | iDestruct "H" as "[]"].
unfold offset_val; eauto.
+
destruct (cenv_cs !! i0) as [co |]; [| iDestruct "H" as "[]"].
destruct (union_field_offset cenv_cs i (co_members co)); [| iDestruct "H" as "[]"].
destruct p. destruct z; [ | iDestruct "H" as "[]" .. ].
destruct b; [ | iDestruct "H" as "[]"].
simpl.
eauto.
Qed.

Ltac unfold_tc_denote :=
unfold denote_tc_nonzero in *;
unfold isptr in *;
unfold denote_tc_igt in *;
unfold denote_tc_Zle in *;
unfold denote_tc_Zge in *;
unfold denote_tc_samebase in *;
unfold denote_tc_nodivover in *;
unfold denote_tc_initialized in *.

Lemma typecheck_lvalue_Evar:
  forall {CS: compspecs} i t pt Delta rho, typecheck_environ Delta rho -> is_pointer_type pt = true ->
           denote_tc_assert (typecheck_lvalue Delta (Evar i t)) rho ⊢
           ⌜tc_val pt (eval_lvalue (Evar i t) rho)⌝.
Proof.
intros.
unfold typecheck_lvalue.
simpl. unfold eval_var.

unfold typecheck_environ in H.
intuition.
destruct rho.
unfold get_var_type in *.

destruct_var_types i; rewrite -> ?Heqo, ?Heqo0 in *; try rewrite -> eqb_type_eq in *; simpl in *; intuition.
rewrite tc_bool_e; iPureIntro; intros.
remember (type_eq t t0). destruct s; try discriminate.
{
simpl in *.
 unfold is_pointer_type in *.
 destruct pt; try solve [inv H0; simpl in *; auto].
 unfold tc_val.
 simple_if_tac; apply I.
}
{ destruct_glob_types i; rewrite -> ?Heqo1, ?Heqo2 in *; [| iIntros "[]"].
remember (eqb_type t t0).
symmetry in Heqb0. destruct b0; simpl in *; [| iIntros "[]"]. apply eqb_type_true in Heqb0.
subst.
iPureIntro; intros.
unfold tc_val; unfold is_pointer_type in H0;
 destruct pt; try solve [inv H0; reflexivity].
 simple_if_tac; apply I.
}
Qed.

Lemma ptrofs_add_repr_0:
  forall i, Ptrofs.add i (Ptrofs.repr 0) = i.
Proof.
  intros.
 rewrite <- (Ptrofs.repr_unsigned i).
  unfold Ptrofs.add. rewrite !Ptrofs.repr_unsigned. rewrite Ptrofs.unsigned_repr.
  rewrite Z.add_0_r. rewrite Ptrofs.repr_unsigned. auto.
  clear; pose proof Ptrofs.max_signed_pos. pose proof Ptrofs.max_signed_unsigned. lia.
Qed.

Lemma typecheck_expr_sound_Efield:
  forall {CS: compspecs} Delta rho e i t
  (H: typecheck_environ Delta rho)
  (IHe: (denote_tc_assert (typecheck_expr Delta e) rho ⊢
          ⌜tc_val (typeof e) (eval_expr e rho)⌝) /\
          (forall pt : type, is_pointer_type pt = true ->
          denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
          ⌜tc_val pt (eval_lvalue e rho)⌝)),
  denote_tc_assert (typecheck_expr Delta (Efield e i t)) rho ⊢
  ⌜tc_val (typeof (Efield e i t)) (eval_expr (Efield e i t) rho)⌝.
Proof.
intros.
simpl in *. unfold typecheck_expr; fold typecheck_lvalue. super_unfold_lift.
 unfold eval_field, offset_val, deref_noload in *.
iIntros "H".
iAssert (⌜access_mode t = By_reference⌝)%I with "[H]" as %MODE. by (destruct (access_mode t); auto; hnf in H0; try contradiction).
rewrite MODE.
destruct IHe as [IHe IHl].
destruct rho.
rewrite denote_tc_assert_andp.
unfold typecheck_environ in H.
destruct H as [_ [Hve Hge]].
iDestruct (eval_lvalue_ptr with "[H]") as %PTR; first done.
{ by rewrite bi.and_elim_l. }
rewrite (IHl t).
2: { clear - MODE; destruct t; try destruct i; try destruct s; try destruct f; inv MODE; simpl; auto. }
iDestruct "H" as (He) "H".
destruct PTR as (? & ? & H); simpl in H.
destruct (typeof e); try iDestruct "H" as "[]".
+ destruct (cenv_cs !! i0) as [co |]; try iDestruct "H" as "[]".
  destruct (field_offset cenv_cs i (co_members co)) as [ [ ? [|]] |  ]; try iDestruct "H" as "[]".
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H.
  destruct t; auto; inv H.
  destruct f; inv He.
+ destruct (cenv_cs !! i0) as [co |]; try iDestruct "H" as "[]".
  destruct (union_field_offset cenv_cs i (co_members co)) as [ [ ? [|]] |  ]; try iDestruct "H" as "[]";
  destruct z; try iDestruct "H" as "[]".
  destruct (eval_lvalue e (mkEnviron ge ve te)); try now inv H.
  rewrite ptrofs_add_repr_0; auto.
Qed.

Lemma typecheck_lvalue_sound_Efield:
 forall {CS: compspecs} Delta rho e i t pt
 (H: typecheck_environ Delta rho)
 (IHe: (denote_tc_assert (typecheck_expr Delta e) rho ⊢
          ⌜tc_val (typeof e) (eval_expr e rho)⌝) /\
        (forall pt0 : type, is_pointer_type pt0 = true ->
         denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
           ⌜tc_val pt0 (eval_lvalue e rho)⌝))
  (H1: is_pointer_type pt = true),
  denote_tc_assert (typecheck_lvalue Delta (Efield e i t)) rho ⊢
  ⌜tc_val pt (eval_lvalue (Efield e i t) rho)⌝.
Proof.
intros.
simpl in *.
unfold typecheck_lvalue; fold typecheck_lvalue.
rewrite denote_tc_assert_andp.
super_unfold_lift.
destruct IHe as [IHe IHl].
 unfold eval_field,offset_val in *; intuition.
destruct rho.
unfold typecheck_environ in *. intuition.
iIntros "H".
iDestruct (eval_lvalue_ptr with "[H]") as %PTR; first done.
{ by rewrite bi.and_elim_l. }
rewrite (IHl pt); last done.
iDestruct "H" as (Hpt) "H".
remember (eval_lvalue e (mkEnviron ge ve te)). unfold isptr in *.
subst v.
destruct PTR as [b [ofs ?]].
destruct (typeof e); try iDestruct "H" as "[]".
+ destruct (cenv_cs !! i0) as [co |]; try iDestruct "H" as "[]".
  destruct (field_offset cenv_cs i (co_members co)) as [ [ ? [|]] |  ]; try iDestruct "H" as "[]".
  iPureIntro; intros.
  rewrite H2.
  destruct pt; inv H1; simpl; auto.
  red; simple_if_tac; apply I.
+ destruct (cenv_cs !! i0) as [co |]; try iDestruct "H" as "[]".
  destruct (union_field_offset cenv_cs i (co_members co)) as [ [ ? [|]] |  ]; try iDestruct "H" as "[]".
  2: destruct z; iDestruct "H" as "[]".
  destruct z; try iDestruct "H" as "[]".
  iPureIntro; intros.
  rewrite H2 in Hpt |- *.
  rewrite ptrofs_add_repr_0; auto.
Qed.

Lemma typecheck_expr_sound_Evar:
  forall {CS: compspecs} Delta rho i t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta (Evar i t)) rho ⊢
  ⌜tc_val (typeof (Evar i t)) (eval_expr (Evar i t) rho)⌝.
Proof.
intros.
unfold typecheck_expr.
iIntros "H".
iAssert (⌜access_mode t = By_reference⌝)%I with "[H]" as %MODE. by (destruct (access_mode t); auto; try contradiction).
rewrite MODE.
simpl.

unfold typecheck_environ in H. intuition.
destruct rho.
unfold get_var_type in *.

unfold eval_var.
destruct_var_types i; rewrite -> ?Heqo, ?Heqo0 in *;
try rewrite -> eqb_type_eq in *; simpl in *; intuition.
- rewrite tc_bool_e; iDestruct "H" as %?; iPureIntro.
remember (type_eq t t0). destruct s; try discriminate.
 subst.
 simpl.
destruct t0; try destruct i0; try destruct s; try destruct f; inv MODE; simpl; auto.
- destruct_glob_types i; rewrite -> ?Heqo1, ?Heqo2 in *; [| iDestruct "H" as "[]"].
rewrite tc_bool_e; iDestruct "H" as %?; iPureIntro.
remember (eqb_type t t0).
symmetry in Heqb0. destruct b0; simpl in *; [| done].
apply eqb_type_true in Heqb0.
subst.
unfold typecheck_glob_environ in *.
destruct t0 as [| [| | |] [|] | | [|] | | | | |]; inv MODE; simpl; auto.
Qed.

Definition unOp_result_type op t :=
match op with
  | Cop.Onotbool =>match t with
                                | Tint _ _ _ => Tint IBool Signed noattr
                                | Tlong _ _ => Tint IBool Signed noattr
                                | Tpointer _ _ => Tint I32 Signed noattr
                                | Tfloat _ _ => Tint IBool Signed noattr
                                | Tarray _ _ _ => Tint IBool Signed noattr
                                | Tfunction _ _ _ => Tint IBool Signed noattr
                                | _ => Tvoid
                                end
  | Cop.Onotint => match t with
                                | Tint _ _ _ => Tint I32 Signed noattr
                                | Tlong _ _ => Tlong Signed noattr
                                | _ => Tvoid
                                end
  | Cop.Oneg => match t with
                           | Tint _ _ _ => Tint I32 Signed noattr
                           | Tlong _ _ => Tlong Signed noattr
                           | Tfloat _ _ => t
                           | _ => Tvoid
                           end
  | Cop.Oabsfloat => t
end.


Lemma tc_val_of_bool_int_type:
 forall b t, is_int_type t = true ->
  tc_val t (bool2val b).
Proof.
 intros.
 destruct t as [ | [ | | | ] [ | ] | | [ | ] | | | | | ];
 try inv H; destruct b; simpl; try split; auto;
rewrite <- Z.leb_le; reflexivity.
Qed.

Lemma typecheck_unop_sound:
 forall {CS: compspecs} Delta rho u e t
 (H: typecheck_environ Delta rho)
 (IHe: (denote_tc_assert (typecheck_expr Delta e) rho ⊢
          ⌜tc_val (typeof e) (eval_expr e rho)⌝) /\
          (forall pt : type,
           is_pointer_type pt = true ->
           denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
           ⌜tc_val pt (eval_lvalue e rho)⌝)),
  denote_tc_assert (typecheck_expr Delta (Eunop u e t)) rho ⊢
  ⌜tc_val t (eval_expr (Eunop u e t) rho)⌝.
Proof.
intros.
unfold typecheck_expr; fold typecheck_expr.
rewrite denote_tc_assert_andp /=.
destruct IHe as [IHe _].
rewrite IHe. iIntros "[H %H2]".
unfold_lift.
clear IHe.
unfold eval_unop, sem_unary_operation, force_val1.
Local Opaque eqb_type.
destruct u; unfold tc_val in H2; simpl;
unfold sem_notbool, sem_notint, sem_neg, sem_absfloat, bool_val;
destruct (typeof e) as [ | [ | | | ] [ | ] | | [ | ] | | | | | ];
 try done; rewrite ?denote_tc_assert_andp /= ?tc_bool_e; unfold_lift;
(iDestruct "H" as "%" || (rewrite ?assoc; iDestruct "H" as "[% _]")); iPureIntro;
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: (if eqb_type ?T1 ?T2 then _ else _) _ |- _ =>
   let J := fresh "J" in
   destruct (eqb_type T1 T2) eqn:J;
   [apply eqb_type_true in J | apply eqb_type_false in J]
end;
 destruct (eval_expr e rho) eqn:?; try done;
 try solve [apply tc_val_of_bool_int_type; auto].
all: try solve [
  destruct t as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; 
  match goal with H: _ _ = true |- _ => inv H end;
            try reflexivity; auto;
             unfold tc_val; try split; auto;
             rewrite <- Z.leb_le; reflexivity].
Qed.

Lemma same_base_tc_val : forall v t1 t2,
same_base_type t1 t2 = true ->
tc_val t1 v ->
 tc_val t2 v.
Proof.
intros. destruct t1; destruct t2;
    try destruct f; try destruct f0; try destruct f1;
   unfold tc_val in *; 
 try match type of H0 with (if ?A then _ else _) _ => 
         destruct A eqn:?J;
         [apply  eqb_type_true in J | apply eqb_type_false in J]
    end;
   try solve [inv H]; destruct v; auto;
   try solve [inv H0];
   try solve [simple_if_tac; apply I].
   unfold same_base_type in H.
   destruct (eqb_type (Tpointer t2 a0) int_or_ptr_type).
   apply I. inv H0. reflexivity.
   unfold same_base_type in H.
   destruct (eqb_type (Tpointer t2 a) int_or_ptr_type).
   apply I. inv H0. reflexivity.
Qed.

Lemma typecheck_temp_sound:
  forall {CS: compspecs} Delta rho (i : ident) t,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_expr Delta (Etempvar i t)) rho ⊢
  ⌜tc_val (typeof (Etempvar i t)) (eval_expr (Etempvar i t) rho)⌝.
Proof.
intros.
simpl. unfold typecheck_expr. destruct rho.
destruct H as [H1 _].
unfold typecheck_temp_environ in *.
unfold eval_id, force_val in *.

simpl.
destruct Delta; simpl in *.
unfold temp_types in *. simpl in *.
specialize (H1 i).
destruct (tyc_temps !! i) eqn: Hty; try (iIntros "[]").
destruct (H1 _ eq_refl) as (v & H & Ht0). clear H1.
rewrite H.
destruct (is_neutral_cast t0 t) eqn:?.
+ simpl.
  unfold denote_tc_initialized.
  iPureIntro; intros H0.
  rewrite H in H0.
  destruct H0 as [? [? ?]].
  inv H0.
  symmetry in Heqb; eapply neutral_cast_subsumption; eauto.
+ destruct (same_base_type t0 t) eqn:?; [ | iIntros "[]"].
  simpl.
  unfold denote_tc_initialized.
  iPureIntro; intros H0.
  rewrite H in H0.
  destruct H0 as [? [? ?]].
  inv H0.
  eapply same_base_tc_val; eauto.
Qed.

Lemma typecheck_deref_sound:
  forall {CS: compspecs} Delta rho e t pt,
   typecheck_environ Delta rho -> is_pointer_type pt = true ->
   (denote_tc_assert (typecheck_expr Delta e) rho ⊢
    ⌜tc_val (typeof e) (eval_expr e rho)⌝) /\
    (forall pt0 : type,
     denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
     ⌜is_pointer_type pt0 = true -> tc_val pt0 (eval_lvalue e rho)⌝) ->
     denote_tc_assert (typecheck_lvalue Delta (Ederef e t)) rho ⊢
    ⌜tc_val pt (eval_lvalue (Ederef e t) rho)⌝.
Proof.
intros until pt. intros H H0 IHe.
unfold typecheck_lvalue; fold typecheck_expr.
rewrite !denote_tc_assert_andp tc_bool_e.
iIntros "[[H %H1] %]".
destruct IHe as [-> _]; iPureIntro; intros.
revert H1; case_eq (is_pointer_type (typeof e)); intros; hnf in H1; try discriminate.
simpl.
destruct (eval_expr e rho); try contradiction.
destruct pt; try solve [inv H0; reflexivity].
unfold tc_val.
unfold is_pointer_type in H0.
destruct (eqb_type (Tpointer pt a) int_or_ptr_type); inv H0.
apply I.
Qed.

End mpred.
