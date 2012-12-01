Load loadpath.
Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Require Export veric.environ_lemmas. 
Require Import veric.binop_lemmas.
Require Import veric.binop_lemmas2. 
Import Cop.

(*Definitions of some environments*)
Definition mkEnviron' (ge: Clight.genv) (ve: venviron) (te: tenviron) :=
  mkEnviron (filter_genv ge) ve te.

Definition empty_genv := (Globalenvs.Genv.empty_genv fundef type).
Definition empty_tenv := PTree.empty val.

Definition empty_environ : environ :=
mkEnviron (filter_genv empty_genv) (Map.empty _) (Map.empty _).

Definition Delta1 : tycontext := (PTree.set 1%positive (type_int32s, false) 
                                 (PTree.empty (type * bool)),
                                 PTree.empty type, Tvoid,PTree.empty _).

Lemma Zlt_bool_rev: forall x y, Zlt_bool x y = Zgt_bool y x.
Proof.
intros. pose proof (Zlt_cases x y). pose proof (Zgt_cases y x).
destruct (Zlt_bool x y); destruct (Zgt_bool y x); auto;
elimtype False; omega.
Qed.

Lemma Zle_bool_rev: forall x y, Zle_bool x y = Zge_bool y x.
Proof.
intros. pose proof (Zle_cases x y). pose proof (Zge_cases y x).
destruct (Zle_bool x y); destruct (Zge_bool y x); auto;
elimtype False; omega.
Qed.

Lemma Zlt_bool_opp: forall x y, Zlt_bool x y = negb (Zge_bool x y).
Proof.
intros. pose proof (Zlt_cases x y). pose proof (Zge_cases x y).
destruct (Zlt_bool x y); destruct (Zge_bool x y); auto.
elimtype False; omega.
Qed.

Lemma Zgt_bool_opp: forall x y, Zgt_bool x y = negb (Zle_bool x y).
Proof.
intros. pose proof (Zgt_cases x y). pose proof (Zle_cases x y).
destruct (Zgt_bool x y); destruct (Zle_bool x y); auto.
elimtype False; omega.
Qed.

Lemma type_eq_true : forall a b, proj_sumbool  (type_eq a b) =true  -> a = b.
Proof. intros. destruct (type_eq a b). auto. simpl in H. inv H.
Qed.



Lemma classify_add_int_cases_both : forall i1 s1 a1 i2 s2 a2,
exists s3, classify_add (Tint i1 s1 a1) (Tint i2 s2 a2)  = add_case_ii s3.
Proof.
intros; destruct i1; destruct s1; destruct i2; destruct s2; eexists;  
unfold classify_add; simpl; eauto.
Qed.

Lemma undef_not_typecheck : forall t, typecheck_val Vundef t = false.
intros.
destruct t; auto.
Qed.


Lemma is_true_true : forall b, is_true b -> b = true.
Proof.
auto.
Qed.



Ltac revert_all := repeat match goal with
| [H: _ |- _] => revert H
end.



 
(*Typechecking soundness*)

Lemma eval_lvalue_ptr : forall rho e (Delta: tycontext) te ve ge,
mkEnviron ge ve te = rho -> 
tc_ve_denote ve (var_types Delta) -> 
tc_ge_denote ge (glob_types Delta) ->
denote_tc_assert (typecheck_lvalue Delta e) rho ->
eval_lvalue e rho = Vundef \/ exists base, exists ofs, eval_lvalue e rho  = Vptr base ofs.
Proof. 
intros.
induction e; eauto.
simpl. unfold eval_var. 
remember (Map.get (ve_of rho) i). destruct o; try rewrite eqb_type_eq; intuition;
try destruct p; try rewrite eqb_type_eq; simpl; try remember (type_eq t t0); try destruct s;
simpl; try remember (negb (type_is_volatile t0));try destruct b0; auto;
try solve[right; eauto].
remember (ge_of rho i); try rewrite eqb_type_eq; simpl.
destruct o; try rewrite eqb_type_eq; simpl; eauto.
destruct p; try rewrite eqb_type_eq; simpl; eauto.
if_tac; eauto.
unfold tc_ve_denote in *. simpl in H2.
unfold get_var_type in *. 
remember ((var_types Delta) ! i).
destruct o. subst. simpl in H2.
unfold lift2 in *.
try rewrite eqb_type_eq in *; simpl in *; intuition.
symmetry in Heqo1.
specialize (H0 i t1 Heqo1).
destruct H0. congruence.
remember ((glob_types Delta) ! i). destruct o; simpl in *; try congruence. 
unfold lift2 in *. right. unfold tc_ge_denote in H1.
symmetry in Heqo2. 
specialize (H1 _ _ Heqo2). destruct H1 as [b [i0 [? ?]]].
rewrite <- H in *.  simpl ge_of in Heqo0. rewrite H1 in *.
inv Heqo0. eauto. inv H2. 



simpl in *. intuition. unfold lift1,lift2,lift0,force_ptr in *. 
destruct (eval_expr e rho); eauto.

simpl in *. unfold lift1,lift0,lift2 in *. destruct H2 as [[? ?] ?]. 
spec IHe; auto. destruct IHe. 
unfold eval_field. unfold eval_struct_field.
destruct (eval_lvalue e rho); eauto;
destruct (typeof e); try congruence; auto.
destruct (field_offset i f); eauto.
unfold eval_field. unfold eval_struct_field.
destruct (eval_lvalue e rho); eauto;
destruct (typeof e); try congruence; auto;
try destruct (field_offset i f); eauto.
try destruct (field_offset i f0); eauto.
Qed. 
 

Transparent Float.intoffloat.
Transparent Float.intuoffloat.

Ltac unfold_tc_denote :=
unfold denote_tc_nonzero in *;
unfold denote_tc_isptr in *;
unfold denote_tc_igt in *;
unfold denote_tc_Zle in *;
unfold denote_tc_Zge in *;
unfold denote_tc_samebase in *;
unfold denote_tc_nodivover in *;
unfold denote_tc_initialized in *.

Lemma typecheck_both_sound: 
  forall Delta rho e , 
             typecheck_environ rho Delta = true ->
             (denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr e rho) (typeof e) = true) /\
             (forall pt, 
             denote_tc_assert (typecheck_lvalue Delta e) rho ->
             is_pointer_type pt = true -> 
             typecheck_val (eval_lvalue e rho) pt=true).
Proof.

intros. induction e; split; intros; try solve[subst; auto].

(*Const int*)
simpl. subst; destruct t; auto; simpl in H0; inv H0; intuition.

(*Const float*)
simpl in *. subst; destruct t; intuition. 

(*Var*)
simpl in *. unfold eval_var.

assert (tc_mode_denote rho Delta ) as SM. unfold typecheck_environ in H. 
rewrite andb_true_iff in H; intuition. apply typecheck_mode_eqv in H3. auto.
destruct rho. 
apply typecheck_environ_sound in H. destruct H as [_ [? ?]].
unfold tc_ve_denote in *. unfold get_var_type in *. 

remember ((var_types Delta) ! i).
destruct o; try rewrite eqb_type_eq in *; simpl in *; intuition. 
unfold lift2 in H0.
remember (type_eq t t0). destruct s; intuition. 
subst. remember (negb(type_is_volatile t0)). destruct b; intuition. 
clear H3. symmetry in Heqo.
specialize (H i t0 Heqo).

destruct H. 
rewrite H in *. rewrite <- Heqb. rewrite eqb_type_refl in *. destruct pt; auto.
remember ((glob_types Delta) ! i). destruct o; try congruence. 
simpl in *. unfold lift2 in H0. destruct H0. remember (eqb_type t (globtype g)).
symmetry in Heqb. destruct b; simpl in *; try congruence. apply eqb_type_true in Heqb.
subst. unfold tc_mode_denote in *. symmetry in Heqo0.  specialize (SM _ _ Heqo0). 
destruct SM. simpl in H4. unfold Map.get. rewrite H4. 
unfold tc_ge_denote in *. destruct (H2 i g); auto. destruct H5. destruct H5. 
rewrite H5. rewrite eqb_type_refl. auto. destruct H4; congruence.  

inv H0. inv H0. 

(*Temp*)
Focus 1.
simpl in *. destruct rho. apply typecheck_environ_sound in H. intuition.
clear H H3.  
unfold tc_te_denote in *. 
unfold eval_id in *. 

simpl. unfold force_val.
destruct Delta. destruct p. destruct p. 
unfold temp_types in *. simpl in *.
remember (t2 ! i). destruct o.
  symmetry in Heqo.  
  destruct p. specialize (H1 i b _  Heqo). simpl in *.
  rewrite eqb_type_eq in *. destruct H1 as [? [? ?]].
  rewrite H. if_tac in H0; simpl in *; try solve [inv H0].
  destruct (type_eq t t4); try solve [inv H0]. subst; auto. simpl in *. 
  if_tac in H0; inv H0. destruct H1; simpl in *; try congruence. 
  simpl in *. destruct H2. rewrite H in H0. inv H0. auto. 
  if_tac in H0; intuition. 

(*deref*)  
simpl in *. unfold lift2 in *. intuition. specialize (H3 pt).
unfold_tc_denote. unfold lift1 in *.
remember (eval_expr e rho); destruct v;
simpl in *; unfold lift2 in *;
remember (typeof e); destruct t0; intuition; destruct pt; auto.

(*addrof*)
intuition. destruct H0. 
destruct t; auto.


(*Unop*)
intuition; simpl in *. destruct H0. intuition.
unfold eval_unop, lift1. 
destruct u; simpl in *. 

unfold sem_notbool in *.
remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; simpl in *; destruct (eval_expr e rho); intuition;
try of_bool_destruct; try destruct t; intuition.

unfold sem_notint.

remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; simpl in *; destruct (eval_expr e rho); intuition;
try of_bool_destruct; try destruct t; intuition.


unfold sem_neg.

remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; simpl in *; destruct (eval_expr e rho); intuition;
try of_bool_destruct; try destruct t; intuition.

(*binop*)
repeat rewrite andb_true_iff in *; intuition.
clear H4. clear H2. clear H. 
eapply typecheck_binop_sound; eauto.

(* cast *)
simpl in *.
intuition.
unfold lift1,eval_cast.
remember (eval_expr e rho). 
remember (typeof e).
destruct H0.
destruct v; destruct t0; intuition; destruct t; try solve [ intuition;
try destruct i; try destruct i0; try destruct i1; intuition;
unfold sem_cast, classify_cast, cast_float_int, 
    Float.intoffloat, Float.intuoffloat;
 destruct s; auto; try (destruct H3 as [H3a H3b]; hnf in H3a,H3b);
 try rewrite <- Heqv in *; repeat invSome;
 inversion2 H3b H3a;
 hnf in H3b0, H3a0;
 rewrite H3a0; rewrite Zle_bool_rev; rewrite H3b0; auto |

simpl in H3; hnf in H3; simpl; rewrite <- Heqv in *; auto |
destruct i0; destruct s; simpl in *; auto; hnf in H3; try rewrite <- Heqv in *; try contradiction]. 

(*EField*)
simpl in *. unfold lift2,eval_field,eval_struct_field,lift1 in *; intuition. 
specialize  (H3 pt). intuition. remember rho.
destruct e0.
apply typecheck_environ_sound in H. intuition. clear H4.
rewrite Heqe0 in H0.
assert (PTR := eval_lvalue_ptr _ e _ _ _ _ Heqe0 H H8).
rewrite Heqe0 in *. clear Heqe0.
intuition. 
remember (eval_lvalue e rho). unfold denote_tc_isptr in *.
destruct v; intuition; try congruence.
remember (eval_lvalue e rho). destruct H7. destruct H4.
destruct v; intuition; try congruence.
inv H4.
destruct (typeof e); intuition. 
destruct (field_offset i f); intuition.
Qed. 

Definition defined_val v :=
match v with
Vundef => False
| _ => True
end.


Lemma typecheck_expr_sound : forall Delta rho e,
 typecheck_environ rho Delta = true -> 
              denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr e rho) (typeof e) = true.
Proof. intros. 
assert (TC := typecheck_both_sound Delta rho e). intuition. Qed.


Lemma typecheck_lvalue_sound : forall Delta rho e,
  typecheck_environ rho Delta = true ->
  denote_tc_assert (typecheck_lvalue Delta e) rho ->
  (forall pt, 
    is_pointer_type pt = true -> 
    typecheck_val (eval_lvalue e rho) pt=true).
intros. edestruct (typecheck_both_sound _ _ e H).
apply H3; eauto.
Qed.

Lemma get_typed_int:
    forall v att, typecheck_val v (Tint I32 Signed att) = true -> 
                      exists i:int, v = Vint i.
intros; destruct v; inv H; eauto.
Qed.

Definition is_ptr_type (ty: type) : bool :=
  match ty with
  | Tpointer _ _ => true
  | Tarray _ _ _ => true
  | Tfunction _ _ => true
  | Tstruct _ _ _ => true
  | Tunion _ _ _ => true
  | _ => false
end.


Lemma tc_binaryop_nomem : forall b e1 e2 m1 m2 t rho,
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m1) =
sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m2).
Proof.
intros.
destruct b; simpl in *; auto;
 unfold sem_cmp; destruct (classify_cmp (typeof e1) (typeof e2));
   try destruct i; try destruct s; auto; contradiction.
Qed. 

Definition some_pt_type := Tpointer Tvoid noattr.

Lemma filter_genv_zero_ofs : forall ge ge2 b i t,
  filter_genv ge = ge2 ->
    (forall id, ge2 id = Some (Vptr b i, t) ->
      i = Int.zero).
Proof.
intros. unfold filter_genv in *. rewrite <- H in H0.
remember (Genv.find_symbol ge id). destruct o. 
destruct (type_of_global ge b0); inv H0; auto.
inv H0.
Qed.



Lemma eval_binop_relate_fail :
forall (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type) (m : mem),
typecheck_environ rho Delta = true ->
forall (ge : genv) te ve,
rho = construct_rho (filter_genv ge) ve te ->
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
denote_tc_assert (typecheck_expr Delta e1) rho ->
None =
sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) Mem.empty ->
Clight.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
Clight.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
Clight.eval_expr ge ve te m (Ebinop b e1 e2 t) Vundef.
Proof. 
intros. assert (TC1 := typecheck_expr_sound _ _ _ H H1).
assert (TC2 := typecheck_expr_sound _ _ _ H H3).
simpl in *.  
unfold sem_binary_operation in *.

destruct b.

eapply eval_binop_relate_fail_add; eauto.
eapply eval_binop_relate_fail_sub; eauto.
eapply eval_binop_relate_fail_mul; eauto.
eapply eval_binop_relate_fail_div; eauto.
eapply eval_binop_relate_fail_mod; eauto.
eapply eval_binop_relate_fail_and; eauto.
eapply eval_binop_relate_fail_or; eauto.
eapply eval_binop_relate_fail_xor; eauto.
eapply eval_binop_relate_fail_shl; eauto.
eapply eval_binop_relate_fail_shr; eauto.
eapply eval_binop_relate_fail_eq; eauto.
eapply eval_binop_relate_fail_ne; eauto.
eapply eval_binop_relate_fail_lt; eauto.
eapply eval_binop_relate_fail_gt; eauto.
eapply eval_binop_relate_fail_le; eauto.
eapply eval_binop_relate_fail_ge; eauto.
Qed.


Lemma eval_both_relate:
  forall Delta ge te ve rho e m, 
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight.eval_expr ge ve te m e  (eval_expr e rho))
           /\
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight.eval_lvalue ge ve te m e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
Proof. 
intros. generalize dependent ge. induction e; intros;
try solve[intuition; constructor; auto | subst; inv H1]; intuition.

(* var*)
assert (TC_Sound:= typecheck_lvalue_sound).
specialize (TC_Sound Delta rho (Evar i t) H0 H1).
specialize (TC_Sound some_pt_type). simpl in TC_Sound.
specialize (TC_Sound (eq_refl _)). 
 
simpl in *. unfold eval_var in *. 
remember (Map.get (ve_of rho) i); destruct o; try destruct p; 
try rewrite eqb_type_eq in *; simpl in *.
destruct (type_eq t t0); simpl in *; intuition.
subst t0. if_tac; intuition.
exists b. exists Int.zero. intuition. constructor.
unfold Map.get in Heqo. unfold construct_rho in *.
destruct rho; inv H; simpl in *;  auto. 

remember (ge_of rho i). destruct o; try destruct p; auto;
try rewrite eqb_type_eq in *; simpl in *; intuition.
destruct (type_eq t t0); simpl in *. subst t0.

unfold get_var_type in *. 
remember ((var_types Delta) ! i). 
destruct o; try rewrite eqb_type_eq in *; simpl in *; unfold lift2 in *; intuition.
destruct (type_eq t t0); simpl in *; [ | contradiction]. subst t0.
symmetry in Heqo1.
destruct rho.  
apply typecheck_environ_sound in H0.
intuition. unfold tc_ve_denote in *. 
unfold tc_ge_denote in *. 
specialize (H0 i t Heqo1). unfold ge_of in *. unfold Map.get in *. 
destruct H0. simpl in Heqo. congruence.

destruct rho. 
apply typecheck_environ_sound in H0. intuition. unfold tc_ge_denote in *. 
remember ((glob_types Delta) ! i). destruct o; simpl in H1; try congruence.
unfold lift2 in *. destruct H1. 
symmetry in Heqo2. specialize (H4 _ _ Heqo2).  destruct H4. destruct H4. 
destruct H4. simpl in Heqo0. rewrite H4 in *. inv Heqo0. exists x. exists x0. split; auto. 
unfold construct_rho in *. inv H. simpl in Heqo. clear H1. 
remember (filter_genv ge). symmetry in Heqg0. 
assert (ZO := filter_genv_zero_ofs _ _ _ _ _ Heqg0 _ H4).  subst.
apply Clight.eval_Evar_global. auto.  unfold filter_genv in H4.
destruct (Genv.find_symbol ge i). destruct (type_of_global ge b); inv H4; auto. 
congruence.  

unfold filter_genv in H4.
remember (Genv.find_symbol ge i).  destruct o; try congruence.  
assert (x = b). destruct (type_of_global ge b); inv H4; auto. subst.
destruct (type_of_global ge b). inv H4; auto. inv H4. rewrite <- H1 in *. simpl in *.
congruence. 
intuition. congruence. 

(*temp*)  
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (Etempvar i t)). simpl in *. 
intuition.  
constructor. unfold eval_id in *. remember (Map.get (te_of rho)  i);
destruct o;  auto. destruct rho; inv H; unfold make_tenv in *.
unfold Map.get in *. auto. 
simpl in *. congruence.

(*deref*)
assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). intuition. simpl in H1.
intuition. simpl. unfold lift1,lift2 in *; unfold_tc_denote.
 remember (eval_expr e rho); destruct v;
intuition. 
exists b. exists i. simpl in *. intuition. constructor.
auto.

(*addrof*)

simpl in H1. unfold lift2 in *.
assert (ISPTR := eval_lvalue_ptr rho e Delta (te_of rho) (ve_of rho) (ge_of rho)).
specialize (IHe ge).
assert (mkEnviron (ge_of rho) (ve_of rho) (te_of rho) = rho). destruct rho; auto.
destruct rho. 
intuition; apply typecheck_environ_sound in H0. intuition. 
simpl. destruct H7. destruct H7. intuition. congruence. 
destruct H7. destruct H7. destruct H7. destruct H1. destruct H1.  simpl in *.
intuition. rewrite H8 in *. constructor. inv H1. auto.

(*unop*)
simpl in *. unfold lift1,lift2,eval_unop in *. intuition. unfold force_val. 
remember (sem_unary_operation u (eval_expr e rho) (typeof e)).
destruct o. eapply Clight.eval_Eunop. eapply IHe; eauto. rewrite Heqo. auto.
apply typecheck_expr_sound in H3; auto. unfold sem_unary_operation in *.
destruct u. simpl in *. remember (typeof e); destruct t0; try inv H2;
try destruct i;try destruct s; try inv H2; simpl in *; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_notbool in *;
simpl in *; inv Heqo. 

simpl in *. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inversion H3; simpl in *; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_notint in *;
simpl in *; inv Heqo. 

simpl in *. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inversion H3; simpl in *; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_neg in *;
simpl in *; inv Heqo.

(*binop*)
simpl in *. unfold lift2,eval_binop in *; intuition. unfold force_val.
remember (sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
(typeof e2) Mem.empty).
destruct o. eapply Clight.eval_Ebinop. eapply IHe1; eauto.
eapply IHe2. apply H. apply H3. auto. apply typecheck_expr_sound in H3; auto.
rewrite Heqo.

apply tc_binaryop_nomem with (t:=t); auto.
specialize (IHe1 ge). specialize (IHe2 ge). intuition.
clear H6 H8. 
eapply eval_binop_relate_fail; eauto.

(*Cast*)
assert (TC := typecheck_expr_sound _ _ _ H0 H1).
simpl in *; unfold lift2,lift1,eval_cast in *; intuition.
unfold force_val. remember (sem_cast (eval_expr e rho) (typeof e) t).
destruct o. eapply Clight.eval_Ecast. eapply IHe. auto. apply H2. auto.


specialize (IHe ge). intuition.

(*Field*)
assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). specialize (TC some_pt_type). intuition. simpl in H1. intuition.
simpl in *. unfold lift2,lift1,eval_field,eval_struct_field in *; remember (eval_lvalue e rho).
destruct H1. destruct H1. specialize (H4 H1).
destruct H4 as [b [ofs H4]].
remember (typeof e) as t0. destruct t0; intuition.
remember (field_offset i f) as r.
destruct r; intuition.
 destruct v; intuition. simpl in *. exists b. exists (Int.add ofs (Int.repr z)). 
intuition. inv H8.
 eapply Clight.eval_Efield_struct; auto.
eapply Clight.eval_Elvalue in H7. apply H7.
rewrite <- Heqt0. auto. apply Clight.deref_loc_copy. simpl; auto.
rewrite <- Heqt0; reflexivity. auto.
inv H8; auto.
subst v.
exists b, ofs. rewrite H8. simpl. split; auto.
eapply Clight.eval_Efield_union; eauto.
eapply Clight.eval_Elvalue; eauto.
rewrite <- Heqt0. apply Clight.deref_loc_copy.
auto. 
Qed. 

Lemma eval_expr_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight.eval_expr ge ve te m e  (eval_expr e rho)).
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.



Lemma eval_lvalue_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight.eval_lvalue ge ve te m e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
apply eval_both_relate.
Qed.

Lemma tc_lvalue_nonvol : forall rho Delta e,
(denote_tc_assert (typecheck_lvalue Delta e) rho) ->
type_is_volatile (typeof e) = false.
Proof.
intros.
destruct e; intuition; simpl in *. 
unfold get_var_type in *. 

destruct ((var_types Delta) ! i); intuition; simpl in *. unfold lift2 in *;
intuition. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; simpl in *; unfold lift2 in *; intuition.

unfold lift2 in *; intuition. unfold tc_bool in *. rewrite if_negb in *.
destruct ((glob_types Delta) ! i). simpl in *. unfold lift2 in *. 
destruct H. if_tac in H0; auto; inv H0. inv H. 

unfold lift2 in *; intuition. clear - H1. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; intuition.

unfold lift2 in *. intuition. unfold tc_bool in *.  rewrite if_negb in *. 
if_tac in H1; auto. inv H1. 
Qed.

(*Proof for "backwards environment checking" that an environment that typechecks
must have come from an update on an environment that typechecks. 
TODO: These Lemmas
should eventually be put in more meaningful places in this file. *)

Lemma join_te_eqv :forall te1 te2 id b1 b2 t1,
te1 ! id = Some (t1, b1) -> te2 ! id = Some (t1, b2) ->
(join_te te1 te2) ! id = Some (t1,andb b1 b2).
Proof.
intros. 
unfold join_te. rewrite PTree.fold_spec. rewrite <- fold_left_rev_right.
assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto. 
assert (forall t, te1 ! id = Some t -> In (id, t) (rev (PTree.elements te1))).
intros. apply In_rev. rewrite rev_involutive. apply PTree.elements_correct.
auto.

induction (rev (PTree.elements te1)). simpl in *.
apply H2 in H. inv H.

simpl in *. destruct a. simpl in *. destruct p0. simpl.
remember (te2 ! p). destruct o. destruct p0.
if_tac. subst. rewrite PTree.gsspec. if_tac. subst. specialize (H1 (t0,b)).
intuition. rewrite H1 in *. inv H.
 rewrite <- Heqo in *. inv H0. auto.
apply IHl; auto. intros. specialize (H2 (t1,b1)). intuition. inv H2. destruct H3; auto. 
specialize (H1 (t1,b1)). intuition.
rewrite H1 in H4. inv H4. auto.
apply IHl; auto.
intros. rewrite H in H4. inv H4. edestruct H2. apply H. inv H4. rewrite H0 in *.
inv Heqo. destruct H3; auto. auto.
apply IHl; auto; intros. rewrite H in *. inv H3. specialize (H2 (t1, b1)).
intuition. inv H2. congruence.
Qed.
 
Lemma temp_types_same_type : forall id i t b Delta,
(temp_types Delta) ! id = Some (t, b) ->
exists b0 : bool,
  (temp_types (initialized i Delta)) ! id = Some (t, b || b0).
Proof.
intros.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o.
destruct p. unfold temp_types in *. simpl. rewrite PTree.gsspec.
if_tac. subst. rewrite H in *. inv Heqo. exists true.   rewrite orb_true_r. 
eauto. exists false.   rewrite orb_false_r. eauto. exists false. rewrite orb_false_r. 
auto. 
Qed.

Lemma temp_types_update_dist : forall d1 d2 ,
(temp_types (join_tycon (d1) (d2))) =
join_te (temp_types (d1)) (temp_types (d2)).
Proof.
intros.
destruct d1; destruct d2. destruct p; destruct p0. destruct p0; destruct p.
simpl. unfold temp_types. simpl. auto.
Qed.

Lemma var_types_update_dist : forall d1 d2 ,
(var_types (join_tycon (d1) (d2))) =
(var_types (d1)).
Proof.
intros.
destruct d1; destruct d2. destruct p; destruct p0. destruct p0; destruct p.
simpl. unfold var_types. simpl. auto.
Qed.


Lemma var_types_update_tycon:
  forall c Delta, var_types (update_tycon Delta c) = var_types Delta.
Proof.
assert (forall i Delta, var_types (initialized i Delta) = var_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); auto. destruct p; auto. 
induction c; intros; simpl; auto.
destruct o; auto.
rewrite IHc2; auto.
rewrite var_types_update_dist. auto.
admit. 
Qed.
 
Lemma glob_types_update_tycon:
  forall c Delta, glob_types (update_tycon Delta c) = glob_types Delta.
Admitted. 

Ltac try_false :=
try  solve[exists false; rewrite orb_false_r; eauto]. 
 
Lemma update_tycon_te_same : forall c Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (update_tycon Delta c)) ! id = Some (t,b || b2)

with update_labeled_te_same : forall ls Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (join_tycon_labeled ls Delta)) ! id = Some (t,b || b2) .
destruct c; intros; simpl; try_false. 

simpl. eapply temp_types_same_type; eauto.

simpl. destruct o; eauto. simpl. eapply temp_types_same_type; eauto.
try_false; eauto. 

assert (forall (c : statement) (Delta : tycontext)
                         (id : positive) (t : type) (b : bool),
                       (temp_types Delta) ! id = Some (t, b) ->
                       exists b2 : bool,
                         (temp_types (update_tycon Delta c)) ! id =
                         Some (t, b || b2)) by auto.
edestruct update_tycon_te_same. apply H.
specialize (update_tycon_te_same c2 _ _ _ _ H1).
destruct (update_tycon_te_same). exists (x || x0). rewrite orb_assoc. eauto. 


simpl. rewrite temp_types_update_dist.

edestruct (update_tycon_te_same c1). apply H.
edestruct (update_tycon_te_same c2). apply H. 
erewrite join_te_eqv;
eauto. exists (x && x0). rewrite orb_andb_distrib_r.  auto.
eauto. eauto. (*these are the problem if it won't qed*) 
(*
intros. destruct ls. simpl. eauto.
simpl. rewrite temp_types_update_dist.
edestruct update_tycon_te_same. apply H.
edestruct update_labeled_te_same. apply H.
exists (x && x0).  
erewrite join_te_eqv. rewrite <- orb_andb_distrib_r. auto. 
eauto. eauto.
*)
Admitted. (*See comment above, "these are the problem" *)


Lemma typecheck_environ_update_te:
  forall rho c Delta, tc_te_denote (te_of rho) (temp_types (update_tycon Delta c)) ->
tc_te_denote (te_of rho) (temp_types Delta)

with typecheck_ls_update_te : forall Delta ty b id l,
(temp_types Delta) ! id = Some (ty, b) -> 
exists b2, (temp_types (join_tycon_labeled l Delta)) ! id = Some (ty, b2).
Proof.
intros. unfold tc_te_denote in *.
destruct c; intros; simpl in *; try solve[eapply H; apply H0].

destruct (eq_dec id i). subst.
destruct (H i true ty). unfold initialized. rewrite H0. 
unfold temp_types. simpl. rewrite PTree.gsspec. rewrite peq_true. 
auto. destruct H1. destruct H2. inv H2. exists x. auto. 
apply H. 
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto.

destruct o.
destruct (eq_dec id i). subst. destruct (H i true ty).
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. inv H0. 
rewrite PTree.gsspec. rewrite peq_true. eauto. congruence.
destruct H1. destruct H2. inv H2. eauto. 
eapply H. unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto. eauto.


destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H1).
edestruct H. apply H2. destruct H3. exists x1. 
split. apply H3. destruct b. auto. auto. 


destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H0).
specialize (H id ((b || x) && (b || x0)) ty ).  
spec H.  
 unfold join_tycon. remember (update_tycon Delta c1).
destruct t. destruct p. destruct p. remember (update_tycon Delta c2).
destruct t3. destruct p. destruct p. unfold temp_types in *.
unfold update_tycon. simpl in *. 

apply join_te_eqv; eauto.    destruct b; auto. simpl in *.
destruct H. exists x1. split. destruct H. auto. left. auto. 

 edestruct (update_labeled_te_same l Delta id).  apply H0. 
 edestruct H. apply H1.  
destruct H2. exists x0. destruct b; auto. 

intros. destruct l; simpl in *.
destruct (update_tycon_te_same s _ _ _ _ H).
eauto.

 destruct (update_tycon_te_same s _ _ _ _ H).
edestruct typecheck_ls_update_te. apply H.
rewrite temp_types_update_dist. erewrite join_te_eqv; eauto.
Qed.

Lemma set_temp_ve : forall Delta i,
var_types (initialized i Delta) = var_types (Delta).
Proof.
intros. destruct Delta. destruct p. destruct p. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (t1 ! i); auto. destruct p; auto.
Qed. 

Lemma set_temp_ge : forall Delta i,
glob_types (initialized i Delta) = glob_types (Delta).
Proof.
intros. destruct Delta. destruct p. destruct p. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (t1 ! i); auto. destruct p; auto.
Qed. 

Lemma update_tycon_same_ve : forall Delta c id v,
(var_types (update_tycon Delta c)) ! id = Some v <->
(var_types (Delta)) ! id = Some v


with update_le_same_ve : forall (l : labeled_statements) (id : positive) (v : type) Delta,
(var_types (join_tycon_labeled l Delta)) ! id = Some v <->
(var_types Delta) ! id = Some v.
Proof.
intros; split; intros.
destruct c; simpl in *; try apply H.
rewrite set_temp_ve in H. auto.
destruct o. rewrite set_temp_ve in H. auto.
auto.
eapply update_tycon_same_ve. rewrite <- update_tycon_same_ve. apply H.

rewrite var_types_update_dist in H.
rewrite update_tycon_same_ve in H. auto.

erewrite update_le_same_ve in H. apply H.

destruct c; simpl in *; try apply H. rewrite set_temp_ve. apply H.
destruct o. rewrite set_temp_ve. apply H.
apply H. rewrite update_tycon_same_ve. rewrite update_tycon_same_ve.
apply H. rewrite var_types_update_dist. 
rewrite update_tycon_same_ve. apply H.
rewrite update_le_same_ve. apply H.

intros. split. intros.
 destruct l. simpl in *. rewrite update_tycon_same_ve in H.
apply H. simpl in *. rewrite var_types_update_dist in H.
rewrite update_tycon_same_ve in H. apply H.

intros. destruct l; simpl in *.
rewrite update_tycon_same_ve. apply H.
rewrite var_types_update_dist.  rewrite update_tycon_same_ve.
apply H.
Qed.   


Lemma glob_types_update_dist :
 forall d1 d2 : tycontext, glob_types (join_tycon d1 d2) = glob_types d1.
destruct d1; destruct d2.  destruct p. destruct p. destruct p0. destruct p. 
auto. 
Qed.

Lemma update_tycon_same_ge : forall Delta c id v,
(glob_types (update_tycon Delta c)) ! id = Some v <->
(glob_types (Delta)) ! id = Some v


with update_le_same_ge : forall (l : labeled_statements) (id : positive) (v : global_spec) Delta,
(glob_types (join_tycon_labeled l Delta)) ! id = Some v <->
(glob_types Delta) ! id = Some v.
Proof.
intros; split; intros.
destruct c; simpl in *; try apply H.
rewrite set_temp_ge in H. auto.
destruct o. rewrite set_temp_ge in H. auto.
auto.
eapply update_tycon_same_ge. rewrite <- update_tycon_same_ge. apply H.

rewrite glob_types_update_dist in H.
rewrite update_tycon_same_ge in H. auto.
erewrite update_le_same_ge in H. apply H.

destruct c; simpl in *; try apply H. rewrite set_temp_ge. apply H.
destruct o. rewrite set_temp_ge. apply H.
apply H. rewrite update_tycon_same_ge. rewrite update_tycon_same_ge.
apply H. rewrite glob_types_update_dist. 
rewrite update_tycon_same_ge. apply H.
rewrite update_le_same_ge. apply H.

intros. split. intros.
 destruct l. simpl in *. rewrite update_tycon_same_ge in H.
apply H. simpl in *. rewrite glob_types_update_dist in H.
rewrite update_tycon_same_ge in H. apply H.

intros. destruct l; simpl in *.
rewrite update_tycon_same_ge. apply H.
rewrite glob_types_update_dist.  rewrite update_tycon_same_ge.
apply H.
Qed.   

Lemma typecheck_environ_update_ve : forall (rho : environ) (c : statement) (Delta : tycontext),
tc_ve_denote (ve_of rho) (var_types (update_tycon Delta c)) ->
tc_ve_denote (ve_of rho) (var_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ve in *; try apply H;
unfold tc_ve_denote in *; intros; apply H; try rewrite var_types_update_dist; 
try apply join_ve_eqv;
repeat rewrite update_tycon_same_ve in *; try rewrite update_le_same_ve;
auto.
Qed. 



Lemma typecheck_environ_update_ge : forall (rho : environ) (c : statement) (Delta : tycontext),
tc_ge_denote (ge_of rho) (glob_types (update_tycon Delta c)) ->
tc_ge_denote (ge_of rho) (glob_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ge in *; try apply H;
unfold tc_ge_denote in *; intros; apply H; try rewrite glob_types_update_dist; 
try apply join_ge_eqv;
repeat rewrite update_tycon_same_ge in *; try rewrite update_le_same_ge;
auto.
Qed. 

Lemma typecheck_environ_update:
  forall rho c Delta, typecheck_environ rho (update_tycon Delta c) = true ->
       typecheck_environ rho Delta = true.
Proof.
intros. unfold typecheck_environ in *. repeat rewrite andb_true_iff in *. 
destruct H. destruct H. destruct H.  split. split. split. clear H0 H1 H2.
rewrite typecheck_te_eqv in *.  intuition.  eapply typecheck_environ_update_te; eauto.

clear H H0 H1. 
rewrite typecheck_ve_eqv in *. eapply typecheck_environ_update_ve.
eauto.

clear H H0 H2. rewrite typecheck_ge_eqv in *. eapply typecheck_environ_update_ge.
eauto.  

clear -H0. rewrite typecheck_mode_eqv in *.  unfold tc_mode_denote in *. 
intros.  
specialize (H0 id t). edestruct H0. rewrite update_tycon_same_ge. auto. 
auto. destruct H1. right. exists x. 
rewrite update_tycon_same_ve in H1. auto. 
Qed. 


Lemma typecheck_bool_val:
  forall v t, typecheck_val v t = true -> bool_type t = true ->
      exists b, strict_bool_val v t = Some b.
Proof.
intros.
destruct t; inv H0;
destruct v; inv H; simpl; try rewrite H1; eauto. 
Qed.

Lemma map_ptree_rel : forall id v te, Map.set id v (make_tenv te) = make_tenv (PTree.set id v te).
intros. unfold Map.set. unfold make_tenv. extensionality. rewrite PTree.gsspec; auto.
Qed.

Lemma cast_exists : forall Delta e2 t rho 
(TC: typecheck_environ rho Delta = true), 
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isCastResultType (typeof e2) t t e2)
  rho ->
sem_cast (eval_expr e2 rho) (typeof e2) t =
Some (force_val (sem_cast (eval_expr e2 rho) (typeof e2) t)).
Proof.
intros. 
assert (exists v, sem_cast (eval_expr e2 rho) (typeof e2) t= Some v).

apply typecheck_expr_sound in H.
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho). 
unfold sem_cast. unfold classify_cast.
Transparent Float.intoffloat.
Transparent Float.intuoffloat.
destruct t; destruct v; destruct t0; simpl in *;
try congruence; try contradiction; eauto;
try solve [
unfold Float.intoffloat, Float.intuoffloat; repeat invSome;
inversion2 H1 H0; hnf in H2,H3; rewrite H3; rewrite Zle_bool_rev; rewrite H2;
simpl; eauto];
try solve [
try destruct i; try destruct s; try destruct i0; try destruct i1; try destruct s0; eauto |

destruct i; destruct s; unfold lift2 in *; try solve[simpl in *; 
  unfold lift2,lift1 in *;  unfold_tc_denote; destruct H0; 
try rewrite <- Heqv in *; 
unfold Float.intoffloat; 
destruct (Float.Zoffloat f0); try contradiction;
try rewrite H0; try rewrite H1; simpl; eauto | 
simpl in *;  unfold Float.intuoffloat; destruct H0;
unfold_tc_denote; try rewrite <- Heqv in *; destruct (Float.Zoffloat f0);
try rewrite H0; try rewrite H1; simpl; eauto; try contradiction] |

try destruct i0; try destruct i1; destruct s; simpl in *; try contradiction; try rewrite H; eauto ].

destruct i; destruct s; unfold lift2 in *;
simpl in *; unfold lift2,lift1 in *;
unfold Float.intoffloat, Float.intuoffloat;
try (
destruct H0 as [H0 H1]; hnf in H0,H1; rewrite <- Heqv in *;
destruct (Float.Zoffloat f0); try contradiction;
hnf in H0,H1; rewrite H0; rewrite Zle_bool_rev; rewrite H1;
simpl; eauto);
simpl; eauto.

auto.
Opaque Float.intoffloat.
Opaque Float.intuoffloat.

destruct H1. rewrite H1. auto.
Qed.


Lemma typecheck_val_eval_cast: 
  forall t2 e2 rho Delta,
      typecheck_environ rho Delta = true ->
      denote_tc_assert (typecheck_expr Delta e2) rho ->
      denote_tc_assert (isCastResultType (typeof e2) t2 t2 e2) rho ->
      typecheck_val (eval_cast (typeof e2) t2 (eval_expr e2 rho)) t2 = true.
Proof. intros ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ H2 H5 H6).
assert (H8 := typecheck_expr_sound _ _ _ H2 H5).
clear - H7 H6 H8.
revert H7; case_eq (sem_cast (eval_expr e2 rho) (typeof e2) t2); intros; inv H7.
unfold eval_cast. rewrite H. simpl.
case_eq (eval_expr e2 rho); intros; rename H0 into H99;
 destruct t2; inv H8; inv H; simpl; auto;
hnf in H6; try contradiction; rewrite H99 in *;
destruct (typeof e2); inv H2; inv H1; auto;
try (unfold sem_cast in H0; simpl in H0;
      destruct i0; simpl in*; destruct s; inv H0; simpl; auto).
simpl in *. unfold lift1 in H6. rewrite H99 in *. inv H6. auto.
simpl in *. unfold isCastResultType in H6. simpl in H6.
unfold sem_cast in H0. 
simpl in H0.
destruct i; simpl in*; destruct s; try destruct f; inv H0; simpl; auto;
invSome; simpl; auto.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
Qed.


Definition func_tycontext_t_denote :=
forall p t id ty b,  list_norepet (map fst p ++ map fst t ) ->   
((make_tycontext_t p t) ! id = Some (ty,b) <-> (In (id,ty) p /\ b=true) \/ (In (id,ty) t /\ b=false)). 

Definition func_tycontext_v_denote :=
forall v id ty, list_norepet (map fst v) ->
((make_tycontext_v v) ! id = Some ty <-> In (id,ty) v). 

Lemma func_tycontext_v_sound : func_tycontext_v_denote. 
unfold func_tycontext_v_denote. intros. 
split; intros; induction v. simpl in *. 
rewrite PTree.gempty in *. congruence. 

simpl in *. destruct a. inv H. rewrite PTree.gsspec in *. if_tac in H0. 
inv H0. auto. intuition. 

inv H0.

simpl in *. destruct a. simpl in *. rewrite PTree.gsspec. destruct H0. 
inv H0. if_tac. auto. intuition. inv H. if_tac. subst. 
clear - H0 H3. rewrite in_map_iff in *. destruct H3. exists (i,ty). auto. 
apply IHv; auto. 
Qed. 
 

Lemma set_inside : forall i0 t1 t p id, 
list_disjoint (map fst p) (i0 :: map fst t) ->
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
          (PTree.set i0 (t1, false)
             (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p) ! id = 
(PTree.set i0 (t1, false) (
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
                (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p)) ! id       
. 
Proof.
intros.
induction t.  
  simpl in *. rewrite PTree.gsspec. 
  if_tac. 
    subst. 
    induction p. 
      simpl in *. rewrite PTree.gsspec. rewrite peq_true. auto.

      simpl in *. rewrite PTree.gsspec. if_tac. subst.
      clear - H. unfold list_disjoint in *. specialize (H (fst a) (fst a)). 
      intuition. apply IHp. unfold list_disjoint in *. intros. 
      apply H; simpl in *; auto.

    induction p. 
       simpl in *. rewrite PTree.gsspec. if_tac. intuition.
       auto. 

       simpl in *.  repeat rewrite PTree.gsspec in *. destruct a.
       simpl in *. if_tac. auto. rewrite IHp.  auto. unfold list_disjoint in *. 
       intros. apply H; simpl in *; auto. 

  simpl in *. rewrite PTree.gsspec in *. if_tac. 
    subst. 
    induction p. 
      simpl in *. rewrite PTree.gsspec in *. rewrite peq_true in *.
      auto.

      simpl in *. rewrite PTree.gsspec in *. destruct a0. simpl in *. 
      if_tac. subst. clear - H. specialize (H p0 p0). intuition.  apply IHp. 
      unfold list_disjoint in *. intros. apply H; simpl in *; auto. 
      intros. apply IHt. unfold list_disjoint in *. intros; simpl in *; apply H;      auto.
      auto. auto. intuition.  

    destruct a. simpl in *. induction p. 
      simpl in *. rewrite PTree.gsspec. if_tac; subst. intuition.
      repeat rewrite PTree.gsspec. auto.  

      simpl in *. destruct a. simpl in *. 
      spec IHt. unfold list_disjoint in *. intros; apply H; simpl in *; auto. 
      intuition. 
      repeat rewrite PTree.gsspec in *. if_tac.
        subst.  auto. 

        apply IHp. unfold list_disjoint in *.   intros. apply H. simpl in *. 
        auto.  auto. intros. auto. 
       
Qed.   

Lemma func_tycontext_t_sound : func_tycontext_t_denote. 
unfold func_tycontext_t_denote.
split; intros;
  unfold make_tycontext_t in *; 
  apply list_norepet_app in H; destruct H as [? [? ?]]. 
  induction t; induction p; simpl in *. 

    rewrite PTree.gempty in *; congruence. 

    left. destruct a; simpl in *. rewrite PTree.gsspec in *. if_tac in H0. 
    inv H0. auto.
    inv H.  destruct IHp; auto. unfold list_disjoint.  intros. inv H4. 
    destruct H. subst. auto. intuition.  

    right. destruct a. simpl in *. rewrite PTree.gsspec in *. 
    if_tac in H0. subst. inv H0. auto. destruct IHt. inv H1; auto. 
    unfold list_disjoint in *. intros. inv H4. auto. intuition. intuition. 


    simpl in *. rewrite PTree.gsspec in *. if_tac in H0. destruct a0. simpl in *.
    subst. inv H0. intuition. destruct a0. simpl in *.  destruct a. simpl in *. 
    destruct IHp. inv H; auto. intro; intros. apply H2; simpl in *; auto. 
    auto. intros. destruct IHt. inv H1; auto. intro; intros; apply H2; simpl in *; auto.
    auto. destruct H7. destruct H7. inv H7. intuition. auto. auto. left. 
    split. right. apply H4. apply H4. right. auto. 


  induction t; induction p; simpl in *. 
    
    intuition. 

    rewrite PTree.gsspec. if_tac. subst. destruct a. simpl in *. 
    destruct H0. destruct H0. destruct H0. inv H0. auto. subst. 
    clear - H H0. inv H. rewrite in_map_iff in *. destruct H3.
    exists (i,ty). auto. inv H0. inv H3. destruct H0. destruct H0. 
    destruct a. destruct H0. subst. inv H0. intuition.

    simpl in *. apply IHp. inv H; auto. intro. intros. inv H6. left.
    subst. auto. destruct H0. inv H0. destruct H0. destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct a. simpl in *. inv H0; subst. 
    rewrite PTree.gsspec. rewrite peq_true. auto. subst. 
    destruct a. simpl in *. rewrite PTree.gsspec. if_tac. 
    subst. clear -H0 H1. inv H1. rewrite in_map_iff in *. 
    destruct H3. exists (i,ty); auto. apply IHt. inv H1; auto. 
    intro; auto. right. auto. 
   
    spec IHt. inv H1; auto.  spec IHt. intro; intros; apply H2; simpl in *; auto.
    spec IHp.  inv H; auto. spec IHp. intro; intros; apply H2; simpl in *; auto. 
    destruct a. destruct a0. destruct H0. simpl in *.
    destruct H0. destruct H0. inv H0.  
    rewrite PTree.gsspec in *. rewrite peq_true. auto. subst. 
    rewrite PTree.gsspec in *. if_tac. subst. inv H. rewrite in_map_iff in H5. 
    destruct H5. exists (i0,ty); auto. spec IHp. auto. spec IHp; auto. 
    
    
    simpl in *. rewrite PTree.gsspec. if_tac. subst. destruct H0. destruct H0.
    inv H0. specialize (H2 i0 i0). destruct H2; simpl; auto. subst. 
    spec IHt. auto. rewrite PTree.gsspec in *. rewrite peq_true in *. auto. 
    
    destruct H0. destruct H0. inv H0. spec IHp. auto. 
    spec IHp; auto. intros; auto. destruct H5. destruct H5; congruence. destruct H5. 
    clear - H5 H1. inv H1. destruct H2. apply in_map_iff. exists (id, ty). auto. subst.
    spec IHp. auto. spec IHp; auto. spec IHt; auto. rewrite PTree.gsspec in *.
    if_tac in IHt. intuition. intros. auto. 

Qed. 

 