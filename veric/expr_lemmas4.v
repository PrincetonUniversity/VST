Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.binop_lemmas5.
Require Import VST.veric.binop_lemmas6.
Require Import VST.veric.expr_lemmas2.
Require Export VST.veric.expr_lemmas3.
Require Import VST.veric.juicy_mem.

Require Import VST.veric.seplog. (*For definition of typecheck_environ*)

Import Cop.
Import Cop2.
Import Clight_Cop2.
Import Ctypes.

Section mpred.

Context `{!heapGS Σ}.

(** Main soundness result for the typechecker **)

Lemma typecheck_both_sound:
  forall {CS: compspecs} Delta rho e ,
             typecheck_environ Delta rho ->
             (denote_tc_assert (typecheck_expr Delta e) rho ⊢
              ⌜tc_val (typeof e) (eval_expr e rho)⌝) /\
             (forall pt, is_pointer_type pt = true ->
             denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
             ⌜tc_val pt (eval_lvalue e rho)⌝).
Proof.
intros. induction e; split; intros; try solve[subst; auto]; try contradiction.

* (*Const int*)
simpl in *. destruct t; try iIntros "[]".
destruct i0; try iIntros "[]". auto.

* (*Const float*)
destruct f; simpl in *; subst; destruct t; try destruct f; auto.
* (* Const single *)
destruct f; simpl in *; subst; destruct t; try destruct f; auto.

* (* Const long *)
simpl in *. destruct t; try iIntros "[]".  auto.
* (*Var*)
eapply typecheck_expr_sound_Evar; eauto.

*
eapply typecheck_lvalue_Evar; eauto.

* (*Temp*)
eapply typecheck_temp_sound; eauto.

* (*deref*)

unfold typecheck_expr; fold typecheck_expr.
destruct (access_mode t) eqn:?H; try iIntros "[]".
rewrite !denote_tc_assert_andp /=.
unfold_lift.
rewrite (proj1 IHe) tc_bool_e; iIntros "[[%He %H1] %H2]".
destruct (eval_expr e rho); inversion H2.
destruct t; try auto; try inversion H0.
- destruct i0, s; inversion H4.
- destruct f; inversion H4.

*

unfold typecheck_lvalue; fold typecheck_expr.
unfold tc_val.
rewrite !denote_tc_assert_andp /=.
unfold_lift.
rewrite (proj1 IHe) tc_bool_e; iIntros "[[%He %H1] %H2]"; iPureIntro.
destruct (eval_expr e rho); try contradiction.
destruct pt; auto; try solve [inversion H0].
destruct (eqb_type (Tpointer pt a) int_or_ptr_type); inv H0; auto.

* (*addrof*)
unfold typecheck_expr; fold typecheck_lvalue.
rewrite denote_tc_assert_andp.
rewrite tc_bool_e; iIntros "[H %]".
rewrite (proj2 IHe); last done.
destruct t; auto.

* (*Unop*)
eapply typecheck_unop_sound; eauto.
* (*binop*)
unfold typecheck_expr; fold typecheck_expr.
rewrite !denote_tc_assert_andp /=.
rewrite (proj1 IHe1) (proj1 IHe2); iIntros "[[H %] %]".
by iApply typecheck_binop_sound.

* (* cast *)
destruct IHe.
eapply typecheck_cast_sound; eauto.

* (*EField*)
eapply typecheck_expr_sound_Efield; eauto.
*
eapply typecheck_lvalue_sound_Efield; eauto.
* (* Esizeof *)
unfold typecheck_expr.
rewrite !denote_tc_assert_andp !tc_bool_e.
iIntros "[%H0 %H1]".
rewrite eqb_type_spec in H1; subst; simpl.
rewrite H0; auto.
* (* Ealignof *)
unfold typecheck_expr.
rewrite !denote_tc_assert_andp !tc_bool_e.
iIntros "[%H0 %H1]".
rewrite eqb_type_spec in H1; subst; simpl.
rewrite H0; auto.
Qed.

Lemma typecheck_expr_sound : forall {CS: compspecs} Delta rho e,
 typecheck_environ Delta rho ->
              denote_tc_assert (typecheck_expr Delta e) rho ⊢
              ⌜tc_val (typeof e) (eval_expr e rho)⌝.
Proof. intros.
assert (TC := typecheck_both_sound Delta rho e). tauto. Qed.

Lemma typecheck_lvalue_sound : forall {CS: compspecs} Delta rho e,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
  ⌜is_pointer_or_null (eval_lvalue e rho)⌝.
Proof.
intros.
destruct (typecheck_both_sound _ _ e H).
apply (H1 (Tpointer Tvoid noattr) (eq_refl _)).
Qed.

Ltac unfold_cop2_sem_cmp :=
unfold Clight_Cop2.sem_cmp, Clight_Cop2.sem_cmp_pl, Clight_Cop2.sem_cmp_lp, Clight_Cop2.sem_cmp_pp.

Definition env_matches (rho : environ) (ge : genv) (ve : env) (te : temp_env) :=
  (forall i, Genv.find_symbol ge i = lookup i (ge_of rho)) /\
  (forall i, ve !! i = lookup i (ve_of rho)) /\
  (forall i, te !! i = lookup i (te_of rho)).

Lemma eval_binop_relate:
 forall {CS: compspecs} Delta (ge: genv) te ve rho b e1 e2 t m
        (Hcenv: cenv_sub (@cenv_cs CS) (genv_cenv ge)),
    (* Do we actually need this? *)
    typecheck_environ Delta rho ->
    (mem_auth m ∗ denote_tc_assert (typecheck_expr Delta e1) rho ⊢
      ⌜Clight.eval_expr ge ve te m e1 (eval_expr e1 rho)⌝) ->
    (mem_auth m ∗ denote_tc_assert (typecheck_expr Delta e2) rho ⊢
      ⌜Clight.eval_expr ge ve te m e2 (eval_expr e2 rho)⌝) ->
    (mem_auth m ∗ denote_tc_assert (typecheck_expr Delta (Ebinop b e1 e2 t)) rho) ⊢
    ⌜Clight.eval_expr ge ve te m (Ebinop b e1 e2 t)
                     (eval_expr (Ebinop b e1 e2 t) rho)⌝.
Proof.
intros.
unfold typecheck_expr; fold typecheck_expr.
simpl in *. super_unfold_lift.
rewrite !denote_tc_assert_andp.
iIntros "[Hm H]".
iDestruct (H0 with "[$Hm H]") as %?.
{ iDestruct "H" as "((_ & $) & _)". }
iDestruct (H1 with "[$Hm H]") as %?.
{ iDestruct "H" as "(_ & $)". }
rewrite !typecheck_expr_sound; try assumption.
iDestruct "H" as "[[H %] %]".
by iApply (eval_binop_relate' with "[$]").
Qed.

Lemma valid_pointer_dry0:
  forall m b ofs, mem_auth m ∗ valid_pointer (Vptr b ofs) ⊢
           ⌜Mem.valid_pointer m b (Ptrofs.unsigned ofs) = true⌝.
Proof.
intros.
rewrite <- (Z.add_0_r (Ptrofs.unsigned ofs)).
apply valid_pointer_dry; auto.
Qed.



Definition some_pt_type := Tpointer Tvoid noattr.

Lemma tc_force_Some : forall ov t, tc_val t (force_val ov)
-> exists v, ov = Some v.
Proof.
  intros.
 unfold tc_val in H.
  destruct (eqb_type t int_or_ptr_type);
 destruct ov; destruct t; eauto; simpl in *; try tauto;
  destruct f; tauto.
Qed.

Lemma typecheck_binop_sound2:
 forall {CS: compspecs} (Delta : tycontext) (rho : environ) (b : binary_operation)
     (e1 e2 : expr) (t : type),
   tc_val (typeof e2) (eval_expr e2 rho) ->
   tc_val (typeof e1) (eval_expr e1 rho) ->
   denote_tc_assert (typecheck_expr Delta e2) rho ∧
   denote_tc_assert (isBinOpResultType b e1 e2 t) rho ∧
   denote_tc_assert (typecheck_expr Delta e1) rho ⊢
   ⌜tc_val t
     (eval_binop b (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho))⌝.
Proof.
intros.
rewrite typecheck_binop_sound; try done.
iIntros "(_ & $ & _)".
Qed.

Lemma eval_binop_relate_fail :
forall {CS: compspecs} (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type) m,
typecheck_environ  Delta rho ->
forall (ge : genv) te ve,
(*rho = construct_rho (filter_genv ge) ve te ->*)
denote_tc_assert (typecheck_expr Delta e2) rho ∧
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ∧
denote_tc_assert (typecheck_expr Delta e1) rho ⊢
⌜None =
sem_binary_operation' b  (typeof e1) (typeof e2) (eval_expr e1 rho) (eval_expr e2 rho) ->
Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
Clight.eval_expr ge ve te m (Ebinop b e1 e2 t) Vundef⌝.
Proof.
intros.
iIntros "H".
iDestruct (typecheck_expr_sound with "[H]") as %?; first done; first iDestruct "H" as "(_ & _ & $)".
iDestruct (typecheck_expr_sound with "[H]") as %?; first done; first iDestruct "H" as "($ & _)".
rewrite typecheck_binop_sound2; try done.
iDestruct "H" as %TC; iPureIntro.
unfold eval_binop, force_val2 in TC.
intros X; rewrite -X in TC.
apply tc_val_Vundef in TC; done.
Qed.

Opaque tc_andp.
(** Equivalence of CompCert eval_expr and our function eval_expr on programs that typecheck **)

Lemma tc_test_eq0:
  forall b i m,
  mem_auth m ∗ denote_tc_test_eq (Vptr b i) (Vint Int.zero) ⊢
  ⌜Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true⌝.
Proof.
intros.
simpl; simple_if_tac; try iIntros "[_ []]".
iIntros "(? & _ & ?)"; iApply weak_valid_pointer_dry; iFrame.
Qed.

Lemma cop2_sem_cast :
    forall t1 t2 v m,
  t1 <> int_or_ptr_type ->
  t2 <> int_or_ptr_type ->
  tc_val t1 v ->
  mem_auth m ∗ (⌜classify_cast t1 t2 = classify_cast size_t tbool⌝ →
   denote_tc_test_eq v (Vint Int.zero)) ⊢
 ⌜Cop.sem_cast v t1 t2 m = sem_cast t1 t2 v⌝.
Proof.
intros.
unfold Cop.sem_cast, sem_cast.
rewrite classify_cast_eq; try by apply eqb_type_false.
destruct (classify_cast t1 t2) eqn: Hclass; destruct Archi.ptr64 eqn: Hp; try discriminate;
destruct v; iIntros "[Hm H]"; try done.
+ apply tc_val_Vundef in H1; contradiction.
+ destruct t1 as [| [| | |] | | [|] | | | | |], t2 as [| [| | |] | | [|] | | | | |]; inv Hclass; try contradiction; simpl in *;
    match goal with
    | H: (if ?A then _ else _) = _ |- _ => destruct A eqn: ?H; inv H
    | H: (if ?A then _ else _) _ |- _ => destruct A eqn: ?H; inv H
    end.
+ destruct t1 as [| [| | |] | | [|] | | | | |], t2 as [| [| | |] | | [|] | | | | |]; inv Hclass; try contradiction; simpl in *;
    match goal with
    | H: (if ?A then _ else _) = _ |- _ => destruct A eqn: ?H; inv H
    | H: (if ?A then _ else _) _ |- _ => destruct A eqn: ?H; inv H
    end.
+ destruct t1 as [| [| | |] | | [|] | | | | |], t2 as [| [| | |] | | [|] | | | | |]; inv Hclass; try contradiction; simpl in *;
    match goal with
    | H: (if ?A then _ else _) = _ |- _ => destruct A eqn: ?H; inv H
    | H: (if ?A then _ else _) _ |- _ => destruct A eqn: ?H; inv H
    end.
+ iAssert (weak_valid_pointer (Vptr b i)) with "[H]" as "H".
  { iSpecialize ("H" with "[%]"); first done.
    simpl.
    simple_if_tac; (iDestruct "H" as "[_ $]" || iDestruct "H" as "[]"). }
  rewrite /Mem.weak_valid_pointer.
  by iDestruct (weak_valid_pointer_dry with "[$H $Hm]") as %->.
Qed.

Ltac destruct_eqb_type := 
match goal with H: context [eqb_type ?t1 ?t2] |- _ =>
 let J := fresh "J" in 
  destruct (eqb_type t1 t2) eqn:?J;
 [apply eqb_type_true in J | apply eqb_type_false in J]
end.

Lemma classify_cast_eq:
 forall t1 t2,
  t1 <> int_or_ptr_type ->
  t2 <> int_or_ptr_type ->
  classify_cast t1 t2 = Cop.classify_cast t1 t2.
Proof.
intros.
destruct t1,t2; try reflexivity;
unfold classify_cast;
try rewrite (proj2 (eqb_type_false _ _) H0);
try rewrite (proj2 (eqb_type_false _ _) H);
reflexivity.
Qed.

Definition cast_pointer_to_bool t1 t2 :=
 match t1 with (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
           match t2 with Tint IBool _ _ => true | _ => false end
 | _ => false
end.

Lemma sem_cast_e1:
 forall t t1 v1 v m,
   sem_cast t t1 v = Some v1 ->
   cast_pointer_to_bool t t1 = false ->
   tc_val t v ->
   Cop.sem_cast v t t1 m = Some v1.
Proof.
intros.
destruct (eqb_type t int_or_ptr_type) eqn:J;
 [apply eqb_type_true in J; subst t
 | apply eqb_type_false in J];
(destruct (eqb_type t1 int_or_ptr_type) eqn:J0;
 [apply eqb_type_true in J0; subst t1
 | apply eqb_type_false in J0]).
* unfold sem_cast, sem_cast_pointer in H; simpl in *.
  rewrite -> N.eqb_refl in *.
  simpl in H.
  inv H.
  destruct v1; auto; inv H1.
*
unfold sem_cast, classify_cast in H.
destruct t1; [auto | | | auto ..].
+
destruct i,s; auto; try solve [destruct v; inv H]; try solve [inv H0];
simpl in H;
simpl;
destruct Archi.ptr64; auto;
destruct v; inv H1; inv H; auto.
+ rewrite <- H; clear H.
  unfold tc_val in H1.
  rewrite eqb_type_refl in H1.
  simpl in H1.
  simpl in *.
  solve [auto | destruct Archi.ptr64 eqn:?Hp; auto; destruct v; inv H1; auto].
+
destruct f; inv H.
+
clear H0.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
destruct v1; inv H1; auto.
*
unfold sem_cast in H.
destruct t; try solve [inv H].
{
  simpl in H.
  rewrite N.eqb_refl in H.
  simpl in H1.
  destruct v; try inv H1.
  simpl.
  destruct Archi.ptr64 eqn:Hp; auto; inv Hp.
}
{
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
unfold tc_val in H1.
rewrite <- eqb_type_spec in J.
destruct (eqb_type (Tpointer t a) int_or_ptr_type); [congruence |].
hnf in H1.
destruct v1; tauto.
}
{
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
unfold tc_val in H1.
hnf in H1.
destruct v1; tauto.
}
{
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
unfold tc_val in H1.
hnf in H1.
destruct v1; tauto.
}
*
revert H.
clear - J J0 H0 H1.
unfold Cop.sem_cast, sem_cast.
unfold Cop.classify_cast, classify_cast, sem_cast_pointer, 
 sem_cast_l2bool, sem_cast_i2bool.
rewrite ?(proj2 (eqb_type_false _ _) J);
rewrite ?(proj2 (eqb_type_false _ _) J0).
destruct t1   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto;
destruct t   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto; try discriminate H0;
 auto;
 destruct Archi.ptr64 eqn:Hp; auto;
 destruct v; auto; try contradiction;
 try solve [simpl in H1; rewrite Hp in H1; inv H1];
 try solve [simpl in H1; revert H1; simple_if_tac; intros []].
 
 simpl in H1; revert H1; simple_if_tac; simpl; rewrite Hp; intros [].
Qed.

Lemma cop2_sem_cast' :
    forall {CS: compspecs} t2 e rho m,
  tc_val (typeof e) (eval_expr e rho) ->
 mem_auth m ∗ denote_tc_assert (isCastResultType (typeof e) t2 e) rho ⊢
 ⌜Cop.sem_cast (eval_expr e rho) (typeof e) t2 m =
  sem_cast (typeof e) t2 (eval_expr e rho)⌝.
Proof.
intros.
iIntros "[Hm H]".
destruct (eq_dec t2 int_or_ptr_type).
{ subst; rewrite isCastR /Cop.sem_cast /sem_cast /classify_cast /= N.eqb_refl.
  destruct (typeof e); try done; destruct Archi.ptr64 eqn: Hp; try done.
  - by simpl in H; (apply is_int_e' in H as [? ->] || apply is_long_e in H as [? ->]).
  - simpl in H.
    revert H; simple_if_tac; intros; destruct (eval_expr e rho); try done.
  - simpl in H.
    revert H; simple_if_tac; intros; destruct (eval_expr e rho); try done.
  - simpl in H.
    revert H; simple_if_tac; intros; destruct (eval_expr e rho); try done. }
destruct (eq_dec (typeof e) int_or_ptr_type).
{ rewrite e0 /tc_val eqb_type_refl /= in H.
  rewrite e0 isCastR /sem_cast; destruct t2; try done; try destruct i; try destruct f; destruct Archi.ptr64; try destruct (intsize_eq _ _);
    rewrite ?N.eqb_refl; unfold_lift; try done;
    destruct (eval_expr e rho) eqn: He; try done. }
rewrite /Cop.sem_cast /sem_cast -classify_cast_eq; try done.
destruct (classify_cast (typeof e) t2) eqn: Hclass; try done.
- destruct t2; try discriminate; try destruct i; try destruct f; destruct (typeof e); try destruct f; try discriminate; simpl in Hclass;
    try solve [destruct (eval_expr e rho); try contradiction; auto];
    try solve [revert Hclass; simple_if_tac; discriminate].
  + simpl in H. revert H; simple_if_tac; destruct (eval_expr e rho); try contradiction; auto.
  + simpl in H. revert H; simple_if_tac; destruct (eval_expr e rho); try contradiction; auto.
- rewrite isCastR Hclass.
  unfold classify_cast in Hclass.
  destruct t2; try destruct i; try destruct f; destruct (typeof e); try destruct f; try discriminate; simpl in *;
    try solve [destruct (eval_expr e rho); try contradiction; auto].
  + destruct (_ && _); try discriminate.
    rewrite denote_tc_assert_test_eq' /= /denote_tc_test_eq; unfold_lift.
    destruct (eval_expr e rho); try contradiction; auto; simpl.
    simple_if_tac; try done.
    iDestruct "H" as "[_ H]".
    by rewrite /Mem.weak_valid_pointer; iDestruct (weak_valid_pointer_dry with "[$Hm $H]") as %->.
  + rewrite denote_tc_assert_test_eq' /= /denote_tc_test_eq; unfold_lift.
    destruct (eval_expr e rho); try contradiction; auto; simpl.
    simple_if_tac; try done.
    iDestruct "H" as "[_ H]".
    by rewrite /Mem.weak_valid_pointer; iDestruct (weak_valid_pointer_dry with "[$Hm $H]") as %->.
  + rewrite denote_tc_assert_test_eq' /= /denote_tc_test_eq; unfold_lift.
    destruct (eval_expr e rho); try contradiction; auto; simpl.
    simple_if_tac; try done.
    iDestruct "H" as "[_ H]".
    by rewrite /Mem.weak_valid_pointer; iDestruct (weak_valid_pointer_dry with "[$Hm $H]") as %->.
Qed.

Lemma isBinOpResultType_binop_stable: forall {CS: compspecs} b e1 e2 t rho,
  denote_tc_assert (isBinOpResultType b e1 e2 t) rho ⊢
  ⌜binop_stable cenv_cs b e1 e2 = true⌝.
Proof.
  intros.
  destruct b; auto;
  unfold isBinOpResultType;
  unfold binop_stable.
  + destruct (classify_add (typeof e1) (typeof e2));
    rewrite ?denote_tc_assert_andp ?tc_bool_e; try iIntros "(((_ & $) & _) & _)"; auto.
  + destruct (classify_sub (typeof e1) (typeof e2));
    rewrite ?denote_tc_assert_andp ?tc_bool_e; try iIntros "(((_ & $) & _) & _)"; auto.
    iIntros "((_ & $) & _)".
Qed.

Lemma cenv_sub_sizeof {ge ge'} (Hcenv : cenv_sub ge' ge): forall t,
  complete_type ge' t = true -> @sizeof ge t = @sizeof ge' t.
Proof.
  induction t; simpl; intros; trivial.
  + rewrite IHt; trivial.
  + specialize (Hcenv i). destruct (Maps.PTree.get i ge'); try congruence. rewrite Hcenv; trivial.
  + specialize (Hcenv i). destruct (Maps.PTree.get i ge'); try congruence. rewrite Hcenv; trivial.
Qed.

Lemma cenv_sub_alignof {ge ge'} (Hcenv : cenv_sub ge' ge): forall t,
  complete_type ge' t = true -> @alignof ge t = @alignof ge' t.
Proof.
  induction t; simpl; intros; trivial.
  + rewrite IHt; trivial.
  + specialize (Hcenv i). destruct (Maps.PTree.get i ge'); try congruence. rewrite Hcenv; trivial.
  + specialize (Hcenv i). destruct (Maps.PTree.get i ge'); try congruence. rewrite Hcenv; trivial.
Qed.

Lemma eval_unop_relate:
 forall {CS: compspecs} Delta (ge: genv) te ve rho u e t m
 (Hcenv: cenv_sub (@cenv_cs CS) (genv_cenv ge))
(* (H : matches_env rho ge ve te) *)
 (H0 : typecheck_environ Delta rho)
 (H1 : mem_auth m ∗ denote_tc_assert (typecheck_expr Delta e) rho ⊢
     ⌜Clight.eval_expr ge ve te m e (eval_expr e rho)⌝)
 (H2 : mem_auth m ∗ denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
     ⌜exists (b : block) (ofs : ptrofs),
       Clight.eval_lvalue ge ve te m e b ofs Full /\
       eval_lvalue e rho = Vptr b ofs⌝),
 mem_auth m ∗ denote_tc_assert (typecheck_expr Delta (Eunop u e t)) rho ⊢
⌜Clight.eval_expr ge ve te m (Eunop u e t)
  (eval_expr (Eunop u e t) rho)⌝.
Proof.
intros.
iIntros "[Hm H]".
iDestruct (typecheck_expr_sound with "H") as %TC; first done.
unfold typecheck_expr; fold typecheck_expr.
unfold eval_expr in TC; fold eval_expr in TC.
simpl; super_unfold_lift.
rewrite denote_tc_assert_andp.
unfold eval_unop in *. unfold force_val1, force_val in *.
remember (sem_unary_operation u (typeof e) (eval_expr e rho)) as o.
destruct o; [|apply tc_val_Vundef in TC; contradiction].
iDestruct (H1 with "[$Hm H]") as %He.
{ iDestruct "H" as "(_ & $)". }
rewrite -bi.pure_mono'; [|intros X; econstructor; [apply He | apply X]].
rewrite typecheck_expr_sound; last done.
iDestruct "H" as "[H %TC']".
destruct u; simpl; destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; try discriminate; simpl in *;
  rewrite ?denote_tc_assert_andp ?tc_bool_e ?negb_true_iff ?notbool_bool_val /Cop.bool_val /classify_bool /= ?bool2val_eq;
  unfold bool_val, bool_val_p in *;
  destruct (eval_expr e rho) eqn:He'; inversion Heqo; auto;
  try (iDestruct "H" as "[%Hptr H]"; rewrite -> Hptr in *; try contradiction).
- by destruct Archi.ptr64; inv H3.
- rewrite denote_tc_assert_test_eq' /=; unfold_lift; rewrite /denote_tc_test_eq He'.
  destruct Archi.ptr64 eqn: Hp; try discriminate; simpl.
  iDestruct "H" as "(% & _ & H)".
  by rewrite /Mem.weak_valid_pointer; iDestruct (weak_valid_pointer_dry with "[$Hm $H]") as %->.
Qed.

Lemma eqb_type_sym: forall a b, eqb_type a b = eqb_type b a.
Proof.
intros.
destruct (eqb_type a b) eqn:?.
rewrite -> eqb_type_spec in Heqb0. subst; symmetry; apply eqb_type_refl.
apply eqb_type_false in Heqb0.
assert (b<>a) by congruence.
rewrite <- eqb_type_spec in H.
destruct (eqb_type b a); auto.
Qed.

Lemma Ptrofs_to_int_repr: 
  Archi.ptr64=false -> 
  forall i, Ptrofs.to_int (Ptrofs.repr i) = Int.repr i.
Proof.
intros.
try solve [inversion H];
unfold Ptrofs.to_int;
apply Int.eqm_samerepr;
change Int.eqm with Ptrofs.eqm;
apply Ptrofs.eqm_sym;
apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma eval_both_relate:
  forall {CS: compspecs} Delta ge te ve rho e m
           (Hcenv : cenv_sub (@cenv_cs CS) (genv_cenv ge)),
           env_matches rho ge ve te ->
           typecheck_environ Delta rho ->
           (mem_auth m ∗ denote_tc_assert (typecheck_expr Delta e) rho ⊢
             ⌜Clight.eval_expr ge ve te m e (eval_expr e rho)⌝)
           /\
           (mem_auth m ∗ denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
             ⌜exists b, exists ofs,
              Clight.eval_lvalue ge ve te m e b ofs Full /\
              eval_lvalue e rho = Vptr b ofs⌝).
Proof.
intros.
induction e; split; iIntros "[Hm H]"; try done; try solve [iPureIntro; constructor; auto].
* (* eval_expr Evar*)
iDestruct (typecheck_expr_sound with "H") as %TC; first done.
simpl in *.
unfold typecheck_expr.
destruct (access_mode t) eqn:MODE; try iDestruct "H" as "[]".
unfold get_var_type, eval_var in *.
remember (lookup i (ve_of rho)) as o; destruct o as [(?, ?)|];
try rewrite eqb_type_eq in *; simpl in *.
rewrite eqb_type_eq in TC |- *; destruct (type_eq t t0); [|apply tc_val_Vundef in TC; contradiction].
subst t0.
iPureIntro.
apply Clight.eval_Elvalue with b Ptrofs.zero Full;
  [ | constructor; simpl; rewrite MODE; auto].
apply eval_Evar_local.
destruct H as (_ & -> & _). symmetry in Heqo; apply Heqo.
unfold typecheck_environ in *.
destruct H0 as [? [Hve Hge]].
hnf in Hve,Hge.
destruct (_ !! _) eqn: Hv.
specialize (Hve i t0). destruct Hve as [Hve _].
destruct (Hve Hv). simpl in *; congruence.
destruct (glob_types Delta !! i) eqn: Hg; [|iDestruct "H" as "[]"].
destruct (Hge _ _ Hg) as [b Hfind]; rewrite Hfind.
iPureIntro.
apply Clight.eval_Elvalue with b Ptrofs.zero Full; [  | econstructor 2; apply MODE].
apply Clight.eval_Evar_global; auto.
{ by destruct H as (_ & -> & _). }
{ by destruct H as (-> & _). }

* (* eval_lvalue Evar *)
 unfold typecheck_lvalue.
 unfold get_var_type.
 unfold eval_lvalue, eval_var.
 destruct_var_types i eqn:HH1&HH2; rewrite -> ?HH1, ?HH2 in *;
  [| destruct_glob_types i eqn:HH3&HH4; rewrite -> ?HH3, ?HH4 in *; [| iDestruct "H" as "[]"]].
 +
 rewrite tc_bool_e; iDestruct "H" as %Heqb0; iPureIntro.
 rewrite Heqb0.
 apply eqb_type_true in Heqb0; subst t0.
 exists b; exists Ptrofs.zero; split; auto.
 constructor; auto.
 by destruct H as (_ & -> & _).
 +
 iPureIntro.
 exists b; exists Ptrofs.zero; split; auto.
 constructor 2; auto.
 { by destruct H as (_ & -> & _). }
 { by destruct H as (-> & _ & _). }

* (*temp*)
iDestruct (typecheck_expr_sound with "H") as %TC; first done.
simpl in *.
iPureIntro.
constructor. unfold eval_id in *. remember (lookup i (te_of rho));
destruct o; subst; auto.
{ by destruct H as (_ & _ & ->). }
{ apply tc_val_Vundef in TC; contradiction. }

* (*deref*)
unfold typecheck_expr; fold typecheck_expr.
destruct (access_mode t) eqn:?H; try done.
rewrite !denote_tc_assert_andp tc_bool_e.
iDestruct "H" as "((H & %) & %)".
iDestruct (proj1 IHe with "[$]") as %?; iPureIntro.
simpl; destruct (eval_expr e rho) eqn:?H; try contradiction.
eapply eval_Elvalue.
econstructor. eassumption.
constructor. auto.
* (*deref*)
unfold typecheck_lvalue; fold typecheck_expr.
rewrite !denote_tc_assert_andp tc_bool_e.
iDestruct "H" as "((H & %) & %)".
iDestruct (proj1 IHe with "[$]") as %?; iPureIntro.
destruct (eval_expr e rho) eqn:?H; try contradiction.
exists b, i. split; auto; constructor; auto.

* (*addrof*)
unfold typecheck_expr; fold typecheck_lvalue.
rewrite !denote_tc_assert_andp tc_bool_e.
iDestruct "H" as "[H %]".
simpl; iDestruct (proj2 IHe with "[$]") as %(b & ? & ? & ->); iPureIntro.
constructor; auto.

* (*unop*)
 destruct IHe; by iApply (eval_unop_relate with "[$]").
* (*binop*)
 destruct IHe1, IHe2; by iApply (eval_binop_relate with "[$]").
* (*Cast*)
iDestruct (typecheck_expr_sound with "H") as %TC; first done.
unfold typecheck_expr; fold typecheck_expr.
rewrite denote_tc_assert_andp.
iDestruct (typecheck_expr_sound with "[H]") as %?; first done.
{ iDestruct "H" as "($ & _)". }
iDestruct (proj1 IHe with "[$Hm H]") as %?.
{ iDestruct "H" as "($ & _)". }
iDestruct "H" as "[_ H]"; iDestruct (cop2_sem_cast' with "[$]") as %?; first done; iPureIntro.
simpl in *; super_unfold_lift; unfold force_val1 in *.
destruct (sem_cast _ _ _); [|apply tc_val_Vundef in TC; contradiction].
econstructor; eauto.
* (*Field*)
 unfold typecheck_expr; fold typecheck_lvalue.
 destruct (access_mode t) eqn:?; try done.
 rewrite denote_tc_assert_andp.
 iDestruct (proj2 IHe with "[$Hm H]") as %He.
 { iDestruct "H" as "($ & _)". }
 iDestruct "H" as "[_ H]".
 destruct He as (b & ofs & ? & He).
 destruct (typeof e) eqn:?; try iDestruct "H" as "[]";
 destruct (cenv_cs !! _) as [co |] eqn:Hco; try iDestruct "H" as "[]".
+
  destruct (field_offset cenv_cs i (co_members co)) as [[?  [|]] |]eqn:?;
    try iDestruct "H" as "[]".
  iPureIntro.
  eapply Clight.eval_Elvalue; eauto.
  eapply Clight.eval_Efield_struct; eauto.
  eapply Clight.eval_Elvalue; auto. eassumption.
  rewrite Heqt0.
  apply Clight.deref_loc_copy; auto.
  { specialize (Hcenv i0); rewrite Hco in Hcenv; apply Hcenv. }
  { instantiate (1:=Full). instantiate (1:=z). rewrite <- Heqr.
    eapply field_offset_stable; try eassumption.
    intros. specialize (Hcenv id); setoid_rewrite -> H2 in Hcenv; apply Hcenv.
    apply co_consistent_complete.
    apply (cenv_consistent i0); auto. }
  simpl; unfold_lift; rewrite Heqt0 /eval_field.
  rewrite He Hco Heqr.
  apply Clight.deref_loc_reference. auto.

+ 
  destruct (union_field_offset (@cenv_cs CS) i (co_members co) ) as [(?, ?)|] eqn:?H; try iDestruct "H" as "[]".
  destruct z; try iDestruct "H" as "[]". destruct b0; try iDestruct "H" as "[]".
  iPureIntro.
  eapply Clight.eval_Elvalue; eauto.
  eapply Clight.eval_Efield_union.
  eapply Clight.eval_Elvalue; eauto.
  apply Clight.deref_loc_copy.
  rewrite Heqt0. auto. eauto.
  { specialize (Hcenv i0); rewrite Hco in Hcenv; apply Hcenv. }
  instantiate (1:=Full). instantiate (1:=0). rewrite <- H2.
  eapply union_field_offset_stable; try eassumption.
  { intros. specialize (Hcenv id); setoid_rewrite H3 in Hcenv; apply Hcenv. }
  { apply co_consistent_complete. 
    apply (cenv_consistent i0); auto. }
  simpl; unfold_lift; rewrite Heqt0 /eval_field.
  rewrite ptrofs_add_repr_0 /= Hco H2.
  rewrite He /=.
  rewrite ptrofs_add_repr_0.
  apply Clight.deref_loc_reference; auto.
*
  iDestruct (typecheck_lvalue_sound with "H") as %TC; first done.
  simpl in TC.
  unfold typecheck_lvalue; fold typecheck_lvalue.
  rewrite denote_tc_assert_andp.
  iDestruct (proj2 IHe with "[$Hm H]") as %He.
  { iDestruct "H" as "($ & _)". }
  iDestruct "H" as "[_ H]".
  destruct He as (b & ofs & ? & He).
  super_unfold_lift; rewrite He in TC.
  destruct (typeof e) eqn:?; try iDestruct "H" as "[]";
    destruct (cenv_cs !! _) as [co |] eqn:Hco; try iDestruct "H" as "[]".
+
destruct (field_offset cenv_cs i (co_members co)) as [(?, ?)|] eqn:?; try iDestruct "H" as "[]".
destruct b0; try iDestruct "H" as "[]".
iPureIntro.
exists b. exists (Ptrofs.add ofs (Ptrofs.repr z)).
simpl; unfold_lift; rewrite Heqt0 /eval_field.
rewrite Hco He Heqr; split; auto.
eapply Clight.eval_Efield_struct; auto; try eassumption.
eapply Clight.eval_Elvalue; eauto.
rewrite Heqt0. apply Clight.deref_loc_copy. simpl; auto.
{ specialize (Hcenv i0); rewrite Hco in Hcenv; apply Hcenv. }
{ rewrite <- Heqr. eapply field_offset_stable; eauto.
  intros. specialize (Hcenv id); setoid_rewrite H2 in Hcenv; apply Hcenv.
  apply co_consistent_complete.
  apply (cenv_consistent i0); auto. }
+
destruct (union_field_offset cenv_cs i (co_members co)) as [(?, ?)|] eqn:?; try iDestruct "H" as "[]".
destruct z; try iDestruct "H" as "[]". destruct b0; try iDestruct "H" as "[]".
iPureIntro.
exists b. exists (Ptrofs.add ofs (Ptrofs.repr 0)).
simpl; unfold_lift; rewrite Heqt0 /eval_field.
rewrite Hco He Heqr; split; auto.
eapply Clight.eval_Efield_union; eauto; try eassumption.
eapply Clight.eval_Elvalue; eauto.
rewrite Heqt0. apply Clight.deref_loc_copy.
auto.
{ specialize (Hcenv i0); rewrite Hco in Hcenv; apply Hcenv. }
rewrite <- Heqr.
apply union_field_offset_stable.
  intros. specialize (Hcenv id); setoid_rewrite H2 in Hcenv; apply Hcenv.
  apply co_consistent_complete.
  apply (cenv_consistent i0); auto.
*
unfold typecheck_expr.
rewrite !denote_tc_assert_andp !tc_bool_e.
iDestruct "H" as "(%H1 & %H2)"; iPureIntro.
rewrite eqb_type_spec in H2; subst.
unfold_lift; simpl.
rewrite H1. unfold expr.sizeof.
rewrite <- (cenv_sub_sizeof Hcenv _ H1).
constructor.
*
unfold typecheck_expr.
rewrite !denote_tc_assert_andp !tc_bool_e.
iDestruct "H" as "(%H1 & %H2)"; iPureIntro.
rewrite eqb_type_spec in H2; subst.
unfold_lift; simpl.
rewrite H1. unfold expr.alignof.
rewrite <- (cenv_sub_alignof Hcenv _ H1).
constructor.
Qed.

Lemma eval_expr_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           cenv_sub (@cenv_cs CS) (genv_cenv ge) ->
           env_matches rho ge ve te ->
           typecheck_environ Delta rho ->
           mem_auth m ∗ denote_tc_assert (typecheck_expr Delta e) rho ⊢
             ⌜Clight.eval_expr ge ve te m e (eval_expr e rho)⌝.
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.

Lemma eval_lvalue_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           cenv_sub (@cenv_cs CS) (genv_cenv ge) ->
           env_matches rho ge ve te ->
           typecheck_environ Delta rho ->
           mem_auth m ∗ denote_tc_assert (typecheck_lvalue Delta e) rho ⊢
             ⌜exists b, exists ofs,
                Clight.eval_lvalue ge ve te m e b ofs Full /\
               eval_lvalue e rho = Vptr b ofs⌝.
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.

End mpred.
