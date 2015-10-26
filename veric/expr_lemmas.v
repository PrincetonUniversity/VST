Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Export veric.environ_lemmas. 
Require Import veric.binop_lemmas2. 
Require Import veric.binop_lemmas. 
Require Import veric.expr_lemmas2.
Require Export veric.expr_lemmas3.
Require Import veric.juicy_mem.
Import Cop.
Import Cop2.

Lemma denote_tc_assert_tc_bool: forall {CS: compspecs} b rho m err,
  denote_tc_assert (tc_bool b err) rho m -> b = true.
Proof.
  intros.
  destruct b; auto.
Qed.

(** Main soundness result for the typechecker **)

Lemma typecheck_both_sound: 
  forall {CS: compspecs} Delta rho m e , 
             typecheck_environ Delta rho ->
             (denote_tc_assert (typecheck_expr Delta e) rho m ->
             typecheck_val (eval_expr e rho) (typeof e) = true) /\
             (forall pt, 
             denote_tc_assert (typecheck_lvalue Delta e) rho m ->
             is_pointer_type pt = true -> 
             typecheck_val (eval_lvalue e rho) pt=true).
Proof.
intros. induction e; split; intros; try solve[subst; auto].

* (*Const int*)
simpl in *. destruct t; try contradiction.
destruct i0; try contradiction. auto.

* (*Const float*)
destruct f; simpl in *; subst; destruct t; try destruct f; intuition.
* (* Const single *)
destruct f; simpl in *; subst; destruct t; try destruct f; intuition. 

* (*Var*)
eapply typecheck_expr_sound_Evar; eauto.

*eapply typecheck_lvalue_Evar; eauto.

* (*Temp*)
eapply typecheck_temp_sound; eauto.

* (*deref*)

simpl in H0 |- *.
unfold deref_noload.
destruct (access_mode t) eqn:?H; try inversion H0.
unfold Datatypes.id.
unfold_lift.
simpl.
rewrite !denote_tc_assert_andp in H0.
simpl in H0.
destruct H0.
unfold_lift in H2.
destruct (eval_expr e rho); inversion H2.
simpl.
destruct t; try reflexivity; try inversion H1.
- destruct i0, s; inversion H4.
- destruct f; inversion H4.

*

simpl in H0 |- *.
rewrite !denote_tc_assert_andp in H0.
simpl in H0.
destruct H0 as [[? ?] ?].
unfold tc_bool in H2; simpl in H2.
destruct (is_pointer_type (typeof e)) eqn:?H; [|inversion H2].
unfold_lift.
unfold_lift in H3.
destruct (eval_expr e rho); inversion H3.
simpl.
destruct pt; try reflexivity; try inversion H1.

* (*addrof*)
intuition.
simpl in *. 
rewrite denote_tc_assert_andp in H0.
destruct H0. 
destruct t; auto.

* (*Unop*)
eapply typecheck_unop_sound; eauto.
* (*binop*)
repeat rewrite andb_true_iff in *; intuition.
clear H4. clear H2. clear H.
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0 as [[H0 E1] E2].
apply (typecheck_binop_sound b Delta rho m e1 e2 t H0 (H3 E2) (H1 E1)).

* (* cast *)
eapply typecheck_cast_sound; eauto.

* (*EField*)
eapply typecheck_expr_sound_Efield; eauto.
*
eapply typecheck_lvalue_sound_Efield; eauto.
* (* Esizeof *)
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0.
apply denote_tc_assert_tc_bool in H0.
apply denote_tc_assert_tc_bool in H1.
rewrite eqb_type_spec in H1.
subst.
reflexivity.
* (* Ealignof *)
simpl in H0.
repeat rewrite denote_tc_assert_andp in H0.
destruct H0.
apply denote_tc_assert_tc_bool in H0.
apply denote_tc_assert_tc_bool in H1.
rewrite eqb_type_spec in H1.
subst.
reflexivity.
Qed.

Lemma typecheck_expr_sound : forall {CS: compspecs} Delta rho m e,
 typecheck_environ Delta rho -> 
              denote_tc_assert (typecheck_expr Delta e) rho m ->
              tc_val (typeof e) (eval_expr e rho).
Proof. intros. 
rewrite tc_val_eq.
assert (TC := typecheck_both_sound Delta rho m e). intuition. Qed.


Lemma typecheck_lvalue_sound : forall {CS: compspecs} Delta rho m e,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_lvalue Delta e) rho m ->
  is_pointer_or_null (eval_lvalue e rho).
Proof.
intros.
 edestruct (typecheck_both_sound _ _ m e H).
specialize (H2 (Tpointer Tvoid noattr) H0 (eq_refl _)).
assert (tc_val (Tpointer Tvoid noattr) (eval_lvalue e rho) = 
      (typecheck_val (eval_lvalue e rho) (Tpointer Tvoid noattr) = true)).
rewrite tc_val_eq; auto.
rewrite <- H3 in H2.
apply H2.
Qed.

Ltac unfold_cop2_sem_cmp :=
unfold Cop2.sem_cmp, Cop2.sem_cmp_pp, Cop2.sem_cmp_pl, Cop2.sem_cmp_lp.

Lemma bin_arith_relate :
forall a b c d v1 v2 t1 t2, 
Cop.sem_binarith a b c d v1 t1 v2 t2 =
sem_binarith a b c d t1 t2 v1 v2.
Proof.
intros. 
unfold Cop.sem_binarith, sem_binarith, Cop.sem_cast, sem_cast, both_int,both_long,both_float,both_single.
destruct (classify_binarith t1 t2); 
 destruct t1 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; simpl; auto;
 destruct v1; auto;                                            
 destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; 
 simpl; auto;
repeat match goal with 
| |- context [match ?v with| Vundef => None| Vint _ => None| Vlong _ => None| Vfloat _ => None| Vsingle _ => None| Vptr _ _ => None end] =>
       destruct v; simpl
| |- context [match ?A with Some _ => None | None => None end] =>
 destruct A; simpl
 end;
 try (destruct (cast_float_int s _); reflexivity);
 try (destruct (cast_float_long s _); reflexivity);
 try (destruct (cast_single_int s _); reflexivity);
 try (destruct (cast_single_long s _); reflexivity);
 auto.
Qed.


Lemma perm_order'_dec_fiddle:
  forall y x, y = Some x ->
     proj_sumbool (Mem.perm_order'_dec y Nonempty) = true.
Proof.
intros. subst. simpl. 
unfold Mem.perm_order_dec. destruct x; reflexivity.
Qed.

Lemma valid_pointer_dry:
  forall b ofs d m, app_pred (valid_pointer' (Vptr b ofs) d) (m_phi m) ->
           Mem.valid_pointer (m_dry m) b (Int.unsigned ofs + d) = true.
Proof.
intros.
simpl in H.
destruct (m_phi m @ (b, Int.unsigned ofs + d)) eqn:?H; try contradiction.
*
pose proof (juicy_mem_access m (b, Int.unsigned ofs + d)).
rewrite H0 in H1.
unfold access_at in H1.
unfold perm_of_res in H1.
simpl in H1. clear H0.
rewrite if_false in H1.
unfold Mem.valid_pointer.
unfold Mem.perm_dec.
eapply perm_order'_dec_fiddle; eauto.
intro; subst t. unfold nonidentity in H. contradiction H.
apply bot_identity.
*
subst.
pose proof (juicy_mem_access m (b, Int.unsigned ofs + d)).
rewrite H0 in H1.
unfold access_at in H1.
unfold perm_of_res in H1.
simpl in H1. clear H0 H.
destruct k.
+
destruct (perm_of_sh_pshare t p).
rewrite H in H1; clear H.
unfold Mem.valid_pointer.
unfold Mem.perm_dec.
eapply perm_order'_dec_fiddle; eauto.
+
unfold Mem.valid_pointer, Mem.perm_dec.
eapply perm_order'_dec_fiddle.
rewrite H1.
reflexivity.
+
unfold Mem.valid_pointer, Mem.perm_dec.
eapply perm_order'_dec_fiddle.
rewrite H1.
reflexivity.
+
unfold Mem.valid_pointer, Mem.perm_dec.
eapply perm_order'_dec_fiddle.
rewrite H1.
reflexivity.
Qed.

Lemma weak_valid_pointer_dry:
  forall b ofs m, app_pred (weak_valid_pointer (Vptr b ofs)) (m_phi m) ->
           (Mem.valid_pointer (m_dry m) b (Int.unsigned ofs) 
           || Mem.valid_pointer (m_dry m) b (Int.unsigned ofs - 1))%bool = true.
Proof.
intros.
rewrite orb_true_iff.
destruct H; [left  | right].
rewrite <- (Z.add_0_r (Int.unsigned ofs)).
apply valid_pointer_dry; auto.
rewrite <- Z.add_opp_r.
apply valid_pointer_dry; auto.
Qed.

Lemma comparable_relate:
  forall v1 v2 op m,
     (denote_tc_comparable v1 v2)
         (m_phi m) ->
     option_map Val.of_bool
     (Val.cmpu_bool (Mem.valid_pointer (m_dry m)) op v1 v2) =
     sem_cmp_pp op true2 v1 v2.
Proof.
intros.
unfold denote_tc_comparable in H.
 destruct v1; try contradiction; auto;
 destruct v2; try contradiction; auto.
*
 unfold sem_cmp_pp; simpl.
 destruct H.
 hnf in H. subst i; rewrite Int.eq_true. simpl.
 apply valid_pointer_dry in H0.
 rewrite Z.add_0_r in H0. rewrite H0. simpl. auto.
*
 unfold sem_cmp_pp; simpl.
 destruct H.
 hnf in H. subst i0; rewrite Int.eq_true. simpl.
 apply valid_pointer_dry in H0.
 rewrite Z.add_0_r in H0. rewrite H0. simpl. auto.
*
 unfold sem_cmp_pp; simpl.
 unfold comparable_ptrs in *.
 unfold sameblock in H.
 destruct (peq b b0); 
  simpl proj_sumbool in H; cbv iota in H;
 [rewrite !if_true by auto | rewrite !if_false by auto].
 destruct H.
 apply weak_valid_pointer_dry in H.
 apply weak_valid_pointer_dry in H0.
 rewrite H. rewrite H0.
 simpl.
 reflexivity.
 destruct H.
 apply valid_pointer_dry in H.
 apply valid_pointer_dry in H0.
 rewrite Z.add_0_r in H,H0.
 rewrite H. rewrite H0.
 reflexivity.
Qed.

Lemma tc_binaryop_relate : forall {CS: compspecs} b e1 e2 t rho m ,
denote_tc_assert (isBinOpResultType b e1 e2 t) rho (m_phi m) ->
Cop.sem_binary_operation cenv_cs b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m_dry m) =
sem_binary_operation' b (typeof e1) (typeof e2) true2 (eval_expr e1 rho) (eval_expr e2 rho).
Proof.
intros.
unfold Cop.sem_binary_operation.
unfold sem_binary_operation'.
destruct b; auto;
repeat match goal with 
    |- ?op1 _ _ _ _ = ?op2 _ _ _ _ => unfold op1, op2; try solve [apply bin_arith_relate] 
  | |- ?op1 _ _ _ _ _ = ?op2 _ _ _ _ _ => unfold op1, op2; try solve [apply bin_arith_relate] 
  | |- ?op1 _ _ _ _ _ _ _ = ?op2 _ _ _ _ _ _ _ =>  unfold op1, op2; 
                                                 try solve [apply bin_arith_relate]
  | |- ?op1 _ _ _ _ _ _ _ = ?op2 _ _ _ _ _ _ => unfold op1, op2; try solve [apply bin_arith_relate]
  | |- ?op1 _ _ _ _ _ _ = ?op2 _ _ _ _ _ _ =>  unfold op1, op2; 
                                                 try solve [apply bin_arith_relate]
 end.
*
unfold Cop.sem_add, sem_add.
destruct (classify_add (typeof e1) (typeof e2)); try reflexivity. 
  apply bin_arith_relate.
*
unfold Cop.sem_sub, sem_sub.
 destruct (classify_sub (typeof e1) (typeof e2)); try reflexivity;
  apply bin_arith_relate.
* destruct (classify_shift (typeof e1)(typeof e2)); try reflexivity; apply bin_arith_relate.
* destruct (classify_shift (typeof e1)(typeof e2)); try reflexivity; apply bin_arith_relate.
* unfold isBinOpResultType in H;
    destruct (classify_cmp (typeof e1) (typeof e2));
     try destruct i; try destruct s; auto; try contradiction;
     simpl in H;
     try (rewrite denote_tc_assert_andp in H; destruct H);
     try apply bin_arith_relate.
  +
     rewrite denote_tc_assert_comparable' in H.
     clear t H0.
     simpl in H. unfold_lift in H.
      apply comparable_relate; auto.
  +
     rewrite denote_tc_assert_comparable' in H.
     simpl in H. unfold_lift in H.     
     destruct (eval_expr e1 rho), (eval_expr e2 rho);
   destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in H;       try contradiction; try reflexivity.
  +
     rewrite denote_tc_assert_comparable' in H.
     simpl in H. unfold_lift in H.     
     destruct (eval_expr e1 rho), (eval_expr e2 rho);
   destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in H;       try contradiction; try reflexivity.
* unfold isBinOpResultType in H; destruct (classify_cmp (typeof e1) (typeof e2));
     try destruct i; try destruct s; auto; try contradiction; 
     simpl in H;
     try rewrite denote_tc_assert_andp in H; super_unfold_lift;
     try destruct H;
     rewrite ?denote_tc_assert_orp,
     ?denote_tc_assert_iszero in *;
      try apply bin_arith_relate.
   +
     rewrite denote_tc_assert_comparable' in H.
     clear t H0.
     simpl in H. unfold_lift in H.    
      apply comparable_relate; auto.
   +
     clear H0.
     rewrite denote_tc_assert_comparable' in H.
     simpl in H. unfold_lift in H.     
     destruct (eval_expr e1 rho), (eval_expr e2 rho);
   destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in H;       try contradiction; try reflexivity.
  +
     clear H0.
     rewrite denote_tc_assert_comparable' in H.
     simpl in H. unfold_lift in H.     
     destruct (eval_expr e1 rho), (eval_expr e2 rho);
   destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
    simpl in H;       try contradiction; try reflexivity.   
* unfold isBinOpResultType in H; destruct (classify_cmp (typeof e1) (typeof e2));
     try destruct i; try destruct s; auto; try contradiction; simpl in H;
     try rewrite denote_tc_assert_andp in *; super_unfold_lift.
      apply bin_arith_relate.
* unfold isBinOpResultType in H; destruct (classify_cmp (typeof e1) (typeof e2));
     try destruct i; try destruct s; auto; try contradiction; simpl in H;
     try rewrite denote_tc_assert_andp in *; super_unfold_lift.
      apply bin_arith_relate.
* unfold isBinOpResultType in H; destruct (classify_cmp (typeof e1) (typeof e2));
     try destruct i; try destruct s; auto; try contradiction; simpl in H;
     try rewrite denote_tc_assert_andp in *; super_unfold_lift.
      apply bin_arith_relate.
* unfold isBinOpResultType in H; destruct (classify_cmp (typeof e1) (typeof e2));
     try destruct i; try destruct s; auto; try contradiction; simpl in H;
     try rewrite denote_tc_assert_andp in *; super_unfold_lift.
      apply bin_arith_relate.
Qed.

Definition some_pt_type := Tpointer Tvoid noattr.

Lemma typecheck_force_Some : forall ov t, typecheck_val (force_val ov) t = true
-> exists v, ov = Some v. 
Proof.
intros. destruct ov; destruct t; eauto; simpl in *; congruence. 
Qed. 

Lemma typecheck_binop_sound2:
 forall {CS: compspecs} (Delta : tycontext) (rho : environ) m (b : binary_operation)
     (e1 e2 : expr) (t : type),
   denote_tc_assert (typecheck_expr Delta e2) rho m ->
   denote_tc_assert (isBinOpResultType b e1 e2 t) rho m ->
   denote_tc_assert (typecheck_expr Delta e1) rho m ->
   typecheck_val (eval_expr e2 rho) (typeof e2) = true ->
   typecheck_val (eval_expr e1 rho) (typeof e1) = true ->
   typecheck_val
     (eval_binop b (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true. 
Proof. 
intros. 
pose proof (typecheck_binop_sound).
simpl in H4. unfold_lift in H4. eapply H4; eauto.
Qed. 

Lemma eval_binop_relate_fail :
forall {CS: compspecs} (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type) m,
typecheck_environ  Delta rho ->
forall (ge : genv) te ve,
rho = construct_rho (filter_genv ge) ve te ->
denote_tc_assert (typecheck_expr Delta e2) rho (m_phi m) ->
denote_tc_assert (isBinOpResultType b e1 e2 t) rho (m_phi m) ->
denote_tc_assert (typecheck_expr Delta e1) rho (m_phi m) ->
None =
sem_binary_operation' b  (typeof e1) (typeof e2) true2 (eval_expr e1 rho) (eval_expr e2 rho) ->
Clight.eval_expr ge ve te (m_dry m) e2 (eval_expr e2 rho) ->
Clight.eval_expr ge ve te (m_dry m) e1 (eval_expr e1 rho) ->
Clight.eval_expr ge ve te (m_dry m) (Ebinop b e1 e2 t) Vundef.
Proof.
intros.
assert (TC1 := typecheck_expr_sound _ _ _ _ H H1).
assert (TC2 := typecheck_expr_sound _ _ _ _ H H3).
rewrite tc_val_eq in *.
copy H2.
rewrite den_isBinOpR in H7; simpl in H7.
eapply typecheck_binop_sound2 in H2; eauto.
remember (eval_expr e1 rho); remember (eval_expr e2 rho);
destruct v; destruct v0; 
try solve [apply typecheck_force_Some in H2; destruct H2;
try congruence].
Qed.
  
Opaque tc_andp.
(** Equivalence of CompCert eval_expr and our function eval_expr on programs that typecheck **)

Lemma cop2_sem_cast : 
    forall t1 t2 v, 
   Cop.sem_cast v t1 t2 = sem_cast t1 t2 v.
intros. unfold Cop.sem_cast, sem_cast.
destruct (classify_cast t1 t2);
destruct v; destruct t1; destruct t2; auto.
Qed.

Lemma isBinOpResultType_binop_stable: forall {CS: compspecs} b e1 e2 t rho phi,
  denote_tc_assert (isBinOpResultType b e1 e2 t) rho phi ->
  binop_stable cenv_cs b e1 e2 = true.
Proof.
  intros.
  destruct b; auto;
  unfold isBinOpResultType in H;
  unfold binop_stable.
  + destruct (classify_add (typeof e1) (typeof e2));
    try rewrite !denote_tc_assert_andp in H;
    try destruct H as [[_ ?] _];
    try solve [eapply denote_tc_assert_tc_bool; eauto].
    auto.
  + destruct (classify_sub (typeof e1) (typeof e2));
    try rewrite !denote_tc_assert_andp in H;
    try destruct H as [[_ ?] _];
    try solve [eapply denote_tc_assert_tc_bool; eauto].
    auto.
Qed.

Lemma comparable1:
  forall b i m,
  (denote_tc_comparable (Vptr b i) (Vint Int.zero)) (m_phi m) ->
  Mem.weak_valid_pointer (m_dry m) b (Int.unsigned i) = true.
Proof.
intros.
destruct H.
apply valid_pointer_dry in H0.
rewrite Z.add_0_r in H0.
unfold Mem.weak_valid_pointer;
rewrite orb_true_iff; left; auto.
Qed.

Lemma eval_both_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ Delta rho ->
           (denote_tc_assert (typecheck_expr Delta e) rho (m_phi m) ->
             Clight.eval_expr ge ve te (m_dry m) e  (eval_expr e rho))
           /\
           (denote_tc_assert (typecheck_lvalue Delta e) rho (m_phi m) ->
             exists b, exists ofs, 
              Clight.eval_lvalue ge ve te (m_dry m) e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
Proof. 
intros until m; intro Hcenv; intros.
(*generalize dependent ge.*)
 induction e; intros;
try solve[intuition; constructor; auto | subst; inv H1]; intuition.

* (* eval_expr Evar*)

assert (TC_Sound:= typecheck_expr_sound).
rewrite tc_val_eq in TC_Sound.
specialize (TC_Sound Delta rho _ (Evar i t) H0 H1).
simpl in TC_Sound|-*.
super_unfold_lift.
unfold deref_noload in TC_Sound|-*.
revert TC_Sound; case_eq (access_mode t); intros; try solve [inv TC_Sound].
rename H2 into MODE.

simpl in *. rewrite MODE in H1.
unfold get_var_type, eval_var in *. 
remember (Map.get (ve_of rho) i); destruct o; try destruct p; 
try rewrite eqb_type_eq in *; simpl in *.
destruct (type_eq t t0); simpl in *; intuition.
subst t0.
apply Clight.eval_Elvalue with b Int.zero;
  [ | constructor; simpl; rewrite MODE; auto].
apply eval_Evar_local.
subst rho.
simpl in Heqo. symmetry in Heqo; apply Heqo.
subst rho. 
unfold typecheck_environ in *. 
destruct H0 as [? [Hve [Hge _]]].
hnf in Hve,Hge.
revert H1; case_eq ((var_types Delta) ! i); intros; try contradiction.
specialize (Hve i t0). destruct Hve as [Hve _].
destruct (Hve H0). simpl in *; congruence.
revert H1; case_eq ((glob_types Delta) ! i); intros; try contradiction.
destruct (Hge _ _ H1) as [b [? ?]].
simpl. simpl in H3. 
rewrite H3.

repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
unfold tc_bool in H2.
if_tac in H2; try contradiction.
apply Clight.eval_Elvalue with b Int.zero; [  | econstructor 2; apply MODE].
apply Clight.eval_Evar_global; auto.

* (* eval_lvalue Evar *)
 simpl in H1.
 destruct (get_var_type Delta i) eqn:?; [ | contradiction].
 destruct (eqb_type t t0) eqn:?; inversion H1; clear H1.
 apply eqb_type_true in Heqb; subst t0.
 destruct H0 as [_ [? [? ?]]].
 subst rho; simpl in *.
 hnf in H0,H1.
 unfold get_var_type in Heqo.
 destruct ((var_types Delta)!i) eqn:?; inv Heqo.
 +
 apply H0 in Heqo0. destruct Heqo0 as [b ?];
 exists b; exists Int.zero; split; auto.
 constructor; auto.
 unfold eval_var; simpl. rewrite H.
 rewrite eqb_type_refl. reflexivity.
 +
 destruct ((glob_types Delta)!i) eqn:?; inv H3.
 destruct (H1 _ _ Heqo) as [b [? ?]];
 exists b; exists Int.zero; split; auto.
 specialize (H2 _ _ Heqo).
 simpl in H2.
 destruct H2.
 constructor 2; auto.
 unfold filter_genv in H. destruct (Genv.find_symbol ge i); inv H.
 destruct H2 as [t' ?]. congruence.
 unfold eval_var. simpl.
 specialize (H2 _ _ Heqo).
 destruct H2. simpl in H2. unfold Map.get; rewrite H2.
 rewrite H. auto.
 destruct H2; congruence.

* (*temp*)  
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (m_phi m) (Etempvar i t)). simpl in *. 
intuition.  
constructor. unfold eval_id in *. remember (Map.get (te_of rho)  i);
destruct o;  auto. destruct rho; inv H; unfold make_tenv in *.
unfold Map.get in *. auto. 
simpl in *. destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; contradiction H3.

* (*deref*)
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (m_phi m) (Ederef e t)). simpl in *. 
intuition.  
destruct (access_mode t) eqn:?H; try inversion H3.
rewrite !denote_tc_assert_andp in H3.
destruct H3 as [[? ?] ?].
simpl in H5.
unfold_lift in H5.
unfold_lift.
apply tc_bool_e in H6.
specialize (H1 H3).
hnf in H7.
destruct (eval_expr e rho) eqn:?H; try contradiction.
eapply eval_Elvalue.
econstructor. eassumption.
simpl.
  unfold deref_noload.
  rewrite H4.
  unfold Datatypes.id. constructor. auto.
* (*deref*)
assert (TC:= typecheck_lvalue_sound _ _ _ _ H0 H3).
simpl in *.
rewrite !denote_tc_assert_andp in H3.
destruct H3 as [[? ?] ?].
specialize (H1 H3).
apply tc_bool_e in H4. simpl in H4.
hnf in H5.
destruct (eval_expr e rho) eqn:?; try contradiction.
exists b, i. simpl in *. unfold_lift. rewrite Heqv. intuition. constructor.
auto.
* (*addrof*)

simpl in H3.
rewrite !denote_tc_assert_andp in H3.
destruct H3.
assert (ISPTR := eval_lvalue_ptr rho (m_phi m) e Delta (te_of rho) (ve_of rho) (ge_of rho)).
specialize (H2 H3).
apply tc_bool_e in H4.
assert (mkEnviron (ge_of rho) (ve_of rho) (te_of rho) = rho). destruct rho; auto.
destruct rho. unfold typecheck_environ in *. intuition. 
destruct H2 as [b [? ?]]. intuition. congruence. 
destruct H2 as [b [? ?]]. destruct H8 as [base [ofs ?]].  simpl in *.
intuition. rewrite H8 in *. constructor. inv H11. auto.

* (*unop*)

simpl in *. 
super_unfold_lift.
rewrite denote_tc_assert_andp in H3; destruct H3.
intuition. clear H2.
unfold eval_unop in *. unfold force_val1, force_val. 
remember (sem_unary_operation u (typeof e) (eval_expr e rho)).
eapply Clight.eval_Eunop. eapply H5.  rewrite Heqo.

unfold sem_unary_operation. unfold Cop.sem_unary_operation.
apply typecheck_expr_sound in H4; auto.
destruct u; auto;
  simpl in H3;
  destruct (typeof e) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; simpl;
  hnf in H4; try contradiction;
  try (simpl in H3; rewrite denote_tc_assert_andp in H3; destruct H3 as [H3 H6]);
  destruct (eval_expr e rho) eqn:?; 
  try contradiction; try reflexivity;
 unfold Cop.sem_notbool; simpl;
 unfold tc_comparable in H6; simpl in H6;
 destruct (eval_expr e any_environ) eqn:?; 
 simpl in H6; unfold_lift in H6;
  try solve [apply (eval_expr_any rho) in Heqv0; congruence];
  rewrite Heqv in H6;
  try (rewrite comparable1; auto).
* (*binop*)
simpl in *. 
clear H4 H2. rename H3 into H7.
rewrite !denote_tc_assert_andp in H5.
destruct H5 as [[H2 H3] H4].
rename H7 into H5.
super_unfold_lift.
unfold eval_binop in *; super_unfold_lift; intuition. unfold force_val2, force_val.
remember (sem_binary_operation' b (typeof e1) (typeof e2) true2 (eval_expr e1 rho) (eval_expr e2 rho)).
destruct o. 
  + eapply Clight.eval_Ebinop. eapply H6; eauto.
    eapply H1; assumption.
   rewrite Heqo. clear Heqo.
   rewrite Hcenv.
    eapply tc_binaryop_relate; eauto.
  +
    eapply eval_binop_relate_fail; eassumption.
* (*Cast*) 
assert (TC := typecheck_expr_sound _ _ _ _ H0 H3).
rewrite tc_val_eq in TC.
simpl in *.
rewrite denote_tc_assert_andp in H3.
destruct H3.
unfold force_val1, force_val in *; super_unfold_lift; intuition.
eapply Clight.eval_Ecast.
eapply H5; auto.
rewrite <- cop2_sem_cast in *.
destruct (Cop.sem_cast (eval_expr e rho) (typeof e) t). auto.
inv TC. 

* (*Field*)
 assert (TC := typecheck_expr_sound _ _ _ _ H0 H3).
 clear H1; rename H3 into H1. 
simpl in H1.
 destruct (access_mode t) eqn:?; try solve [inv H1].
 rewrite denote_tc_assert_andp in H1. destruct H1.
 specialize (H2 H1). destruct H2 as [b [ofs [? ?]]].
 destruct (typeof e) eqn:?; try solve[inv H3];
 destruct (cenv_cs ! i0) as [co |] eqn:Hco; try solve [inv H3].
+ 
   destruct (field_offset cenv_cs i (co_members co)) eqn:?;
     try contradiction.
  inv H3. simpl in *.
  unfold deref_noload in *. rewrite Heqm0 in *. 
  eapply Clight.eval_Elvalue; eauto. 
  eapply Clight.eval_Efield_struct; eauto. 
  eapply Clight.eval_Elvalue; auto. eassumption.
  rewrite Heqt0.
  apply Clight.deref_loc_copy. auto.
  rewrite Hcenv; eassumption.
  rewrite Hcenv; eassumption.
  unfold_lift.
  unfold Datatypes.id; simpl.
  rewrite Heqt0. rewrite H4. simpl. rewrite Hco. rewrite Heqr.
   apply Clight.deref_loc_reference. auto.
   
+ unfold deref_noload. simpl. unfold_lift.
   rewrite Heqt0. simpl. rewrite Hco.
  eapply Clight.eval_Elvalue; eauto.
  eapply Clight.eval_Efield_union. 
  eapply Clight.eval_Elvalue; eauto.
  apply Clight.deref_loc_copy.
  rewrite Heqt0. auto. eauto.
  rewrite Hcenv; eauto.
  rewrite H4. simpl.
  unfold deref_noload. rewrite Heqm0.
  apply Clight.deref_loc_reference; auto.
*
 clear H1.
 assert (TC:= typecheck_lvalue_sound _ _ _ _ H0 H3).
 simpl in *.
 rewrite denote_tc_assert_andp in H3. destruct H3.
 unfold eval_field,offset_val in *; super_unfold_lift.
 specialize (H2 H1).
destruct H2 as [b [ofs H4]].
destruct H4.
rewrite H4 in TC|-*.
 destruct (typeof e) eqn:?; try contradiction;
destruct (cenv_cs ! i0) as [co |] eqn:Hco; try solve [inv H3].
+ 
destruct (field_offset cenv_cs i (co_members co)) eqn:?; try contradiction.
exists b. exists (Int.add ofs (Int.repr z)).
intuition.
 eapply Clight.eval_Efield_struct; auto; try eassumption.
eapply Clight.eval_Elvalue in H2. apply H2.
rewrite Heqt0. apply Clight.deref_loc_copy. simpl; auto.
rewrite Hcenv; eassumption.
rewrite Hcenv; eassumption.
+
exists b, ofs. simpl. split; auto.
eapply Clight.eval_Efield_union; eauto.
eapply Clight.eval_Elvalue; eauto.
rewrite Heqt0. apply Clight.deref_loc_copy.
auto.
rewrite Hcenv; eassumption.
*
simpl in H1.
repeat rewrite denote_tc_assert_andp in H1.
destruct H1.
apply denote_tc_assert_tc_bool in H1.
apply denote_tc_assert_tc_bool in H2.
rewrite eqb_type_spec in H2.
subst.
unfold eval_expr.
unfold_lift; simpl.
rewrite <- Hcenv.
constructor.
*
simpl in H1.
repeat rewrite denote_tc_assert_andp in H1.
destruct H1.
apply denote_tc_assert_tc_bool in H1.
apply denote_tc_assert_tc_bool in H2.
unfold eval_expr.
unfold_lift; simpl.
rewrite <- Hcenv.
constructor.
Qed.

Lemma eval_expr_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ Delta rho ->
           (denote_tc_assert (typecheck_expr Delta e) rho (m_phi m) ->
             Clight.eval_expr ge ve te (m_dry m) e  (eval_expr e rho)).
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.

Lemma eval_lvalue_relate:
  forall {CS: compspecs} Delta ge te ve rho e m,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te->
           typecheck_environ Delta rho ->
           (denote_tc_assert (typecheck_lvalue Delta e) rho (m_phi m) ->
             exists b, exists ofs, 
              Clight.eval_lvalue ge ve te (m_dry m) e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.

(*
Lemma tc_lvalue_nonvol : forall rho Delta e,
(denote_tc_assert (typecheck_lvalue Delta e) rho) ->
type_is_volatile (typeof e) = false.
Proof.
intros.
destruct e; intuition; simpl in *. 
unfold get_var_type in *. 

destruct ((var_types Delta) ! i); intuition; simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 super_unfold_lift;
intuition. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; simpl in *; super_unfold_lift; intuition.

super_unfold_lift; intuition. unfold tc_bool in *. rewrite if_negb in *.
destruct ((glob_types Delta) ! i). simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 super_unfold_lift. 
destruct H. if_tac in H0; auto; inv H0. inv H. 


repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift; intuition. clear - H1. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; intuition.

repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift. intuition. unfold tc_bool in *.  rewrite if_negb in *. 
if_tac in H1; auto. inv H1. 
Qed.
*)

Lemma typecheck_environ_update_te:
  forall rho c Delta, typecheck_temp_environ (te_of rho) (temp_types (update_tycon Delta c)) 
     ->
typecheck_temp_environ  (te_of rho) (temp_types Delta)

with typecheck_ls_update_te : forall Delta ty b id l,
(temp_types Delta) ! id = Some (ty, b) -> 
exists b2, (temp_types (join_tycon_labeled l Delta)) ! id = Some (ty, b2).
Proof.
intros. 
unfold typecheck_temp_environ in H. unfold typecheck_temp_environ.  
destruct c; intros; simpl in *; try solve[eapply H; apply H0].
*
destruct (eq_dec id i). subst.
destruct (H i true ty). unfold initialized. rewrite H0. 
unfold temp_types. simpl. rewrite PTree.gsspec. rewrite peq_true. 
auto. destruct H1. destruct H2. inv H2. exists x. auto. 
apply H. 
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto.
*
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
*
destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H1).
destruct (H _ _ _ H2) as [v [? ?]]. exists v.
split; auto. destruct H4; auto. left. destruct b; simpl; auto.
*
destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H0).
specialize (H id ((b || x) && (b || x0))%bool ty ).  
spec H.  
 unfold join_tycon. remember (update_tycon Delta c1).
destruct t. remember (update_tycon Delta c2).
destruct t. unfold temp_types in *.
unfold update_tycon. simpl in *. 
apply join_te_eqv; eauto.    destruct b; auto. simpl in *.
destruct H. exists x1. split. destruct H. auto. left. auto. 
*
 edestruct (update_labeled_te_same l Delta id).  apply H0. 
 edestruct H. apply H1.  
destruct H2. exists x0. split; auto. destruct b; simpl; auto.
* 
intros. destruct l; simpl in *.
exists b; assumption.
 destruct (update_tycon_te_same s _ _ _ _ H).
edestruct typecheck_ls_update_te. apply H.
rewrite temp_types_update_dist. erewrite join_te_eqv; eauto.
Qed.

Lemma typecheck_environ_update_ve : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_var_environ (ve_of rho) (var_types (update_tycon Delta c)) ->
typecheck_var_environ (ve_of rho) (var_types Delta).
Proof.
intros. 
intros id t; specialize (H id t).
destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ve in *;
 try apply H.
repeat rewrite update_tycon_same_ve in *; auto.
rewrite var_types_update_dist, update_tycon_same_ve in H; auto.
rewrite update_le_same_ve in H; auto.
Qed. 



Lemma typecheck_environ_update_ge : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_glob_environ (ge_of rho) (glob_types (update_tycon Delta c)) ->
typecheck_glob_environ (ge_of rho) (glob_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ge in *; try apply H;
unfold typecheck_glob_environ in *; intros; apply H; try rewrite glob_types_update_dist; 
try apply join_ge_eqv;
repeat rewrite update_tycon_same_ge in *; try rewrite update_le_same_ge;
auto.
Qed. 

Lemma typecheck_environ_update:
  forall rho c Delta, typecheck_environ (update_tycon Delta c) rho ->
       typecheck_environ Delta rho.
Proof.
intros. unfold typecheck_environ in *. intuition. 
clear - H0. unfold typecheck_temp_environ in *. 
eapply typecheck_environ_update_te; eauto.

clear -H. eapply typecheck_environ_update_ve; eauto. 

eapply typecheck_environ_update_ge.
eauto.  

clear - H3. 
unfold same_env in *. intros. 
specialize (H3 id t).
repeat rewrite update_tycon_same_ge in *. specialize (H3 H). 
destruct H3; auto. destruct H0. 
rewrite update_tycon_same_ve in *. eauto.
Qed. 

Lemma typecheck_bool_val:
  forall v t, 
       typecheck_val v t = true -> 
       bool_type t = true ->
      exists b, strict_bool_val v t = Some b.
Proof.
intros.
destruct t; try destruct f; inv H0;
destruct v; inv H; simpl; try rewrite H1; eauto. 
Qed.

Lemma map_ptree_rel : forall id v te, Map.set id v (make_tenv te) = make_tenv (PTree.set id v te).
intros. unfold Map.set. unfold make_tenv. extensionality. rewrite PTree.gsspec; auto.
Qed.

Lemma cop_2_sem_cast : forall t1 t2 e,
Cop.sem_cast (e) t1 t2 = Cop2.sem_cast t1 t2 e.
Proof.
intros. unfold Cop.sem_cast, sem_cast.
destruct t1 as [ | [ | | | ] | [ | ] | [ | ] | | | | | ]; 
  destruct t2 as [ | [  | | | ] | [ | ] | [ | ] | | | | | ]; destruct e; simpl; auto.   
Qed.

Lemma cast_exists : forall {CS: compspecs} Delta e2 t rho phi
(TC: typecheck_environ Delta rho), 
denote_tc_assert (typecheck_expr Delta e2) rho phi ->
denote_tc_assert (isCastResultType (typeof e2) t e2)
  rho phi ->
sem_cast (typeof e2) t (eval_expr e2 rho)  =
Some (force_val (sem_cast (typeof e2) t (eval_expr e2 rho))).
Proof.
intros. 
assert (exists v, sem_cast (typeof e2) t (eval_expr e2 rho) = Some v). 
{
apply typecheck_expr_sound in H; [ | auto ].
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho). 
unfold sem_cast. unfold classify_cast.
Transparent liftx.
destruct t as [ | [ | | | ] [ | ] a | i a | [ | ] a | | | | | ]; destruct v;
destruct t0 as [ | [ | | | ] [ | ] ? | i1 ? | [ | ] ? | | | | | ]; simpl in *;
try congruence; try contradiction; eauto;
unfold isCastResultType in *;
simpl in *;
rewrite denote_tc_assert_andp in H0; simpl in H0;
 unfold_lift in H0; rewrite <- Heqv in H0; simpl in H0;
match type of H0 with (app_pred match ?ZZ with Some _ => _ | None => _ end _ /\ _) =>
    destruct ZZ eqn:H5
 end;
 destruct H0; try contradiction;
 (first [rewrite (float_to_int_ok _ _ H5)
        | rewrite (float_to_intu_ok _ _ H5)
        | rewrite (single_to_int_ok _ _ H5)
        | rewrite (single_to_intu_ok _ _ H5)
        ] ;
    [ eexists; reflexivity
    | split; [apply Z.leb_le | apply Z.geb_le]; apply is_true_e; assumption ]).
}
Opaque liftx.
destruct H1. rewrite H1. auto.
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

 Definition cast_no_val_change (from: type)(to:type) : bool :=
match from, to with
| Tint _ _ _, Tint I32 _ _ => true
| Tpointer _ _, Tpointer _ _ => true
| Tfloat F64 _ , Tfloat F64 _ => true
| Tfloat F32 _ , Tfloat F32 _ => true
| _, _ => false
end. 

Lemma cast_no_change : forall v from to,
is_true (typecheck_val v from)  ->
is_true (cast_no_val_change from to) ->
Cop.sem_cast v from to = Some v. 
Proof. 
intros. apply is_true_e in H. apply is_true_e in H0.
destruct v; destruct from as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; 
  simpl in *; try congruence; 
 destruct to as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; simpl in *; try congruence; auto.
Qed. 

Lemma tc_exprlist_length : forall {CS: compspecs} Delta tl el rho phi, 
denote_tc_assert (typecheck_exprlist Delta tl el) rho phi ->
length tl = length el. 
Proof. 
intros. generalize dependent el. induction tl; intros. simpl in *. destruct el. inv H. auto. 
inv H. simpl in H. destruct el; try solve [inv H]. simpl in *.
rewrite !denote_tc_assert_andp in H.
f_equal; apply IHtl.
destruct H; auto.
Qed.

Lemma neutral_cast_typecheck_val : forall {CS: compspecs} e t rho phi Delta,
true = is_neutral_cast (implicit_deref (typeof e)) t ->
denote_tc_assert (isCastResultType (implicit_deref (typeof e)) t  e) rho phi ->
denote_tc_assert (typecheck_expr Delta e) rho phi ->
typecheck_environ Delta rho ->
typecheck_val (eval_expr e rho) t = true. 
Proof.
intros.
rewrite isCastR in H0.
apply typecheck_expr_sound in H1; auto. rewrite tc_val_eq in H1.
Transparent Int.repr.
destruct (typeof e)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] ;
destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; simpl in H; simpl in H0;
try congruence; remember (eval_expr e rho); destruct v;
simpl in H0; try congruence; auto; 
unfold is_neutral_cast in *;
simpl in *; try congruence; super_unfold_lift; 
try rewrite <- Heqv in *;  unfold denote_tc_iszero in *;
try apply H0; try contradiction;
try (rewrite andb_true_iff; repeat rewrite Z.leb_le;
    rewrite orb_true_iff in H1; destruct H1 as [H1|H1];
   apply int_eq_e in H1; subst; compute; split; congruence);
try (repeat rewrite Z.leb_le;
  rewrite orb_true_iff in H1; destruct H1 as [H1|H1];
   apply int_eq_e in H1; subst; compute; congruence).
*
 change Byte.min_signed with (-128) in H1;
 change Byte.max_signed with 127 in H1;
 change (Z.neg (shift_pos 15 1)) with (-32768);
rewrite andb_true_iff in H1|-*; destruct H1 as [H1 H1']; 
  rewrite Z.leb_le in H1,H1'; split; rewrite Z.leb_le;
  omega.
*  
 change Byte.max_unsigned with 255 in H1; 
 rewrite Z.leb_le in H1|-*; omega.
Qed.

Opaque Int.repr.

Definition typecheck_tid_ptr_compare
Delta id := 
match (temp_types Delta) ! id with
| Some (t, _) =>
   is_int_type t 
| None => false
end. 

Lemma typecheck_tid_ptr_compare_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall id, typecheck_tid_ptr_compare Delta id = true ->
                typecheck_tid_ptr_compare Delta' id = true.
Proof.
unfold typecheck_tid_ptr_compare;
intros.
destruct H as [? _].
specialize (H id).
destruct ((temp_types Delta) ! id) as [[? ?]|]; try discriminate.
destruct ((temp_types Delta') ! id) as [[? ?]|]; try contradiction.
 destruct H; subst; auto.
Qed.

Lemma typecheck_val_sem_cast: 
  forall {CS: compspecs} t2 e2 rho phi Delta,
      typecheck_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho phi ->
      denote_tc_assert (isCastResultType (typeof e2) t2  e2) rho phi ->
      typecheck_val (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho))) t2 = true.
Proof. intros ? ? ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ phi H2 H5 H6).
assert (H8 := typecheck_expr_sound _ _ _ _ H2 H5).
rewrite tc_val_eq in H8.
clear - H7 H6 H8.
revert H7; case_eq (sem_cast (typeof e2) t2 (eval_expr e2 rho) ); intros; inv H7.
simpl.
rewrite isCastR in H6.
case_eq (eval_expr e2 rho); intros; rename H0 into H99;
 destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; 
  inv H8; inv H; simpl; auto;
hnf in H6; try contradiction; rewrite H99 in *;
destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; 
inv H2; inv H1; auto;
simpl in H6;
try (unfold sem_cast in H0;
      simpl in*; inv H0; simpl; auto);
super_unfold_lift;
try (rewrite H99 in H6; simpl in H6; try contradiction H6;
      apply is_true_e in H6);
auto;
 try match type of H1 with 
   match ?ZZ with Some _ => _ | None => _ end = _ => 
  destruct ZZ eqn:H5; inv H1; simpl; auto
end;
 try (rewrite andb_true_iff in H1; destruct H1 as [H1 H1']);
 try rewrite orb_true_iff in H1;
 try rewrite Z.leb_le in H1; try rewrite Z.leb_le in H1';
 simpl;
 (transitivity true; [ | symmetry]);
 try rewrite andb_true_iff; try rewrite orb_true_iff;
 repeat rewrite Z.leb_le;
 auto;
 try match goal with
  | |- context [Int.sign_ext ?n ?i] =>
  apply (sign_ext_range' n i);  compute; split; congruence 
  | |- context [Int.zero_ext ?n ?i] =>
  apply (zero_ext_range' n i);  compute; split; congruence 
  end;
try match goal with 
    | |- Int.eq (if ?A then _ else _) _ = true \/ _ =>
     destruct A; simpl; auto
   end.
Qed.







