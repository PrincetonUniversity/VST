Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.malloc_lemmas.
Local Open Scope logic.

Fixpoint fold_right_sepcon' (l: list(environ->mpred)) : environ -> mpred :=
 match l with 
 | nil => emp
 | b::nil => b
 | b::r => b * fold_right_sepcon' r
 end.

Lemma fold_right_sepcon'_eq:
  fold_right_sepcon' = @fold_right (environ->mpred) _ sepcon emp.
Proof.
extensionality l rho.
induction l; auto.
simpl.
destruct l. simpl. rewrite sepcon_emp. auto.
f_equal; auto.
Qed.


Lemma orp_dup {A}{ND: NatDed A}: forall P: A, P || P = P.
Proof. intros. apply pred_ext.
apply orp_left; apply derives_refl.
apply orp_right1; apply derives_refl.
Qed.

Lemma typecheck_glob_environ_e':
 forall ge tc, typecheck_glob_environ ge tc ->
   forall id t, tc ! id = Some t ->
   exists b, ge id = Some (Vptr b Int.zero, globtype t) /\
                typecheck_val (Vptr b Int.zero) (globtype t) = true.
Proof.
intros.
destruct (H _ _ H0) as [b [j [? ?]]].
assert (j=Int.zero) by admit.   (* need to work on this.  It's
   guaranteed by CompCert but our logic loses track of this fact. *)
subst. eauto.
Qed.


Lemma address_mapsto_zeros_memory_block:
 forall sh n b,
  0 <= n <= Int.max_unsigned ->
  address_mapsto_zeros sh (nat_of_Z n) (b, 0) |--
  memory_block sh (Int.repr n) (Vptr b Int.zero).
Proof.
intros.
Transparent memory_block.
 unfold memory_block.
Opaque memory_block.
 rewrite Int.unsigned_repr by auto.
rewrite Int.unsigned_zero.
 assert (exists i, i=0) as [i ?] by eauto.
 rewrite <- H0.
 assert (0 <= i) by omega.
 assert (i + n <= Int.max_unsigned).
 subst. omega.
 rewrite <- (Z2Nat.id n) in H2 by omega.
 change nat_of_Z with Z.to_nat.
 clear - H1 H2.
 forget (Z.to_nat n) as n'.
 revert i H1 H2;  induction n'; intros.
 simpl; auto.
 rewrite inj_S in H2. unfold Z.succ in H2.
 apply sepcon_derives; auto.
 unfold mapsto_, umapsto.
 apply orp_right2.
 rewrite prop_true_andp by auto.
 apply exp_right with (Vint Int.zero).
 rewrite Int.unsigned_repr by omega. 
 auto.
 fold address_mapsto_zeros. fold memory_block'.
 apply IHn'. omega. omega.
Qed.


Lemma tc_globalvar_sound:
  forall Delta i t gv rho, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (Global_var t) ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = Init_space (sizeof t) :: nil ->
   gvar_readonly gv = false ->
   sizeof t <= Int.max_unsigned ->
   tc_environ Delta rho ->
   globvar2pred(i, gv) rho |-- 
   typed_mapsto_ Ews t (eval_var i t rho).
Proof.
intros.
unfold globvar2pred.
simpl.
destruct H6 as [? [? [? ?]]].
destruct (H9 i _ H0); [ | destruct H10; congruence].
destruct (typecheck_glob_environ_e' _ _ H8 _ _ H0) as [b [? ?]].
rewrite H11. rewrite H1.
rewrite H3; simpl.
unfold eval_var.
unfold Map.get. rewrite H10. rewrite H11.
simpl. rewrite eqb_type_refl.
rewrite H4.
simpl.
change (Share.splice extern_retainer Tsh) with Ews.
rewrite sepcon_emp.
rewrite <- memory_block_typed.
apply address_mapsto_zeros_memory_block.
pose (sizeof_pos t); omega.
Qed.

Lemma tc_globalvar_sound':
  forall Delta i t gv, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (Global_var t) ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = Init_space (sizeof t) :: nil ->
   gvar_readonly gv = false ->
   sizeof t <= Int.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
   `(typed_mapsto_ Ews t) (eval_var i t).
Proof.
intros.
go_lowerx.
eapply tc_globalvar_sound; eauto.
Qed.

Lemma main_pre_eq:
 forall prog u, main_pre prog u = 
  fold_right_sepcon' (map globvar2pred (prog_vars prog)).
Proof.
intros. rewrite fold_right_sepcon'_eq; reflexivity.
Qed.

Definition expand_globvars (Delta: tycontext)  (R R': list (environ -> mpred)) :=
 forall rho, 
    tc_environ Delta rho ->
  SEPx R rho |-- SEPx R' rho.

Lemma do_expand_globvars:
 forall R' Espec Delta P Q R c Post,
 expand_globvars Delta R R' ->
 @semax Espec Delta (PROPx P (LOCALx Q (SEPx R'))) c Post ->
 @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; [ | apply H0].
clear H0.
go_lower.
normalize.
Qed.

Lemma do_expand_globvars_cons: 
   forall Delta A A' R R',
  local (tc_environ Delta) && A |-- A' ->
  expand_globvars Delta R R' ->
  expand_globvars Delta (A::R) (A'::R').
Proof.
intros.
hnf in H|-*.
intros.
apply sepcon_derives; auto.
specialize (H rho).
simpl in H. unfold local in H.
eapply derives_trans; [ | apply H].
apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma do_expand_globvars_nil:
  forall Delta, expand_globvars Delta nil nil.
Proof.
intros. hnf; intros.
auto.
Qed.

Ltac expand_one_globvar :=
 (* given a proof goal of the form   local (tc_environ Delta) && globvar2pred (_,_) |-- ?33 *)
first [
    eapply tc_globalvar_sound';
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
      | reflexivity | compute; congruence ]
 | apply andp_left2; apply derives_refl
 ].

Ltac expand_main_pre := 
 rewrite main_pre_eq; simpl fold_right_sepcon;
 eapply do_expand_globvars;
 [repeat 
   (eapply do_expand_globvars_cons;
    [ expand_one_globvar | ]);
   apply do_expand_globvars_nil
 |  ].


