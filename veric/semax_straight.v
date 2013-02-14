Load loadpath.
Require Import veric.base.
Require Import msl.normalize.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import compositional_compcert.extspec.
Require Import compositional_compcert.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.
 
Open Local Scope pred.

Section extensions.
Context {Z} (Hspec: juicy_ext_spec Z).

Lemma semax_straight_simple:
 forall Delta (B: assert) P c Q,
  (forall rho, boxy extendM (B rho)) ->
  (forall jm jm1 ge ve te rho k F, 
              app_pred (B rho) (m_phi jm) ->
              guard_environ Delta (current_function k) rho ->
              closed_wrt_modvars c F ->
              rho = construct_rho (filter_genv ge) ve te  ->
              age jm jm1 ->
              ((F rho * |>P rho) && funassert Delta rho) (m_phi jm) ->
              exists jm', exists te', exists rho',
                rho' = mkEnviron (ge_of rho) (ve_of rho) (make_tenv te') /\
                level jm = S (level jm') /\
                guard_environ (update_tycon Delta c) (current_function k) rho'  /\
                jstep cl_core_sem ge (State ve te (Kseq c :: k)) jm 
                                 (State ve te' k) jm' /\
              ((F rho' * Q rho') && funassert Delta rho) (m_phi jm')) ->
  semax Hspec Delta (fun rho => B rho && |> P rho) c (normal_ret_assert Q).
Proof.
intros until Q; intros EB Hc.
rewrite semax_unfold. 
intros psi n _ k F Hcl Hsafe te ve w Hx w0 H Hglob.
apply nec_nat in Hx.
apply (pred_nec_hereditary _ _ _ Hx) in Hsafe.
clear n Hx.
apply (pred_nec_hereditary _ _ _ (necR_nat H)) in Hsafe.
clear H w.
rename w0 into w.
apply assert_safe_last'; intro Hage.
intros ora jm _ H2. subst w.
rewrite andp_assoc in Hglob.
destruct Hglob as [TC'  Hglob].
apply can_age_jm in Hage; destruct Hage as [jm1 Hage].
destruct Hglob as [Hglob Hglob'].
apply extend_sepcon_andp in Hglob; auto.
destruct Hglob as [TC2 Hglob].
specialize (Hc jm  jm1 psi ve te _ k F TC2 TC' Hcl (eq_refl _) Hage (conj Hglob Hglob')); clear Hglob Hglob'.
destruct Hc as [jm' [te' [rho' [H9 [H2 [TC'' [H3 H4]]]]]]].
change (@level rmap _  (m_phi jm) = S (level (m_phi jm'))) in H2.
rewrite H2 in Hsafe.
eapply safe_step'_back2; [eassumption | ].
unfold rguard in Hsafe.
specialize (Hsafe EK_normal None te' ve).
simpl exit_cont in Hsafe.
specialize (Hsafe (m_phi jm')).
spec Hsafe.
change R.rmap with rmap; omega.
specialize (Hsafe _ (necR_refl _)).
spec Hsafe.
split; auto.
subst rho'; auto.
destruct H4; split; auto.
subst rho'.
unfold normal_ret_assert.
unfold frame_ret_assert in *.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
rewrite sepcon_comm; auto.
replace (funassert (exit_tycon c Delta EK_normal)) with (funassert Delta); auto.
apply same_glob_funassert; simpl; auto. rewrite glob_types_update_tycon; auto.
subst rho'. 
hnf in Hsafe.
change R.rmap with rmap in *.
replace (@level rmap compcert_rmaps.R.ag_rmap (m_phi jm) - 1)%nat with (@level rmap compcert_rmaps.R.ag_rmap (m_phi jm'))%nat by omega.
apply Hsafe; auto.
Qed.


Definition is_comparison op :=
match op with 
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => true              
  | _ => false
end. 


(* work in progress... 
Lemma semax_set_forward_ptr_compare : 
forall (Delta: tycontext) (P: assert) id cmp e1 e2 ty,
    is_comparison cmp = true  ->
    is_pointer_type (typeof e1) = true ->
    is_pointer_type (typeof e2) = true -> 
    semax Hspec Delta 
        (fun rho => 
          |> (tc_expr Delta e1 rho && tc_expr Delta e2 rho  && 
          (tc_temp_id id ty Delta (Ebinop cmp e1 e2 ty) rho) && P rho)) 
          (Sset id (Ebinop cmp e1 e2 ty)) 
        (normal_ret_assert 
          (fun rho => (EX old:val, 
                 !! (eval_id id rho =  subst id old (eval_expr (Ebinop cmp e1 e2 ty)) rho) &&
                            subst id old P rho))).
Proof. 
intros until ty.
replace (fun rho : environ =>
   |> (tc_expr Delta e1 rho && tc_expr Delta e2 rho  && 
          (tc_temp_id id ty Delta (Ebinop cmp e1 e2 ty) rho) && P rho))
 with (fun rho : environ =>
     (|> tc_expr Delta e1 rho &&
      |> tc_expr Delta e2 rho &&
      |> tc_temp_id id ty Delta (Ebinop cmp e1 e2 ty) rho &&
      |> P rho))
  by (extensionality rho;  repeat rewrite later_andp; auto).
intros CMP PT1 PT2. 
apply semax_straight_simple; auto. 
intros jm jm' ge vx tx rho k F [[TC3 TC1] TC2] TC' Hcl Hge ? ?.
specialize (TC3 (m_phi jm') (age_laterR (age_jm_phi H))).
specialize (TC2 (m_phi jm') (age_laterR (age_jm_phi H))). 
specialize (TC1 (m_phi jm') (age_laterR (age_jm_phi H))). 
exists jm', (PTree.set id (eval_expr (Ebinop cmp e1 e2 ty) rho) (tx)).
econstructor.
split.
reflexivity.
split3; auto.
apply age_level; auto.
normalize in H0.
clear - TC' TC2 TC3 TC1 CMP PT1 PT2  Hge.
simpl in *. simpl. rewrite <- map_ptree_rel.
apply guard_environ_put_te'; auto. subst; simpl in *.
unfold construct_rho in *; auto.
intros. simpl in *. unfold typecheck_temp_id in *.
rewrite H in TC2.
destruct t as [t b]; simpl in *.
rewrite tc_andp_sound in *; simpl in *. 
unfold_coerce. destruct TC2. 
unfold tc_bool in *. remember (is_neutral_cast (ty) t). 
destruct b0; inv H0. unfold guard_environ in *. 
destruct TC' as [TC' TC'']. 
apply typecheck_both_sound in TC3; auto.
apply typecheck_both_sound in TC1; auto. 

unfold eval_binop. unfold Cop.sem_binary_operation.
destruct cmp; simpl in *; try congruence. unfold Cop.sem_cmp. 

remember(typeof e1); remember (typeof e2);   
destruct t0; destruct t1; simpl in *; try congruence.  
simpl in *;
destruct (eval_expr e1 (construct_rho (filter_genv ge) vx            tx)); try solve [inv TC3]; 
destruct (eval_expr e2 (construct_rho (filter_genv ge) vx tx)); try solve [inv TC1]. simpl.
unfold Val.of_bool. destruct t; if_tac; simpl in *; try congruence; try solve [inv H1]; destruct ty; auto.  simpl in H1. unfold_coerce. 

try destruct i; try destruct s; try destruct i0; try destruct s0; simpl in *; destruct t; auto. unfold Val.of_bool.

apply neutral_cast_typecheck_val with (Delta := Delta); auto. 
unfold guard_environ in *. destruct TC'; auto. 
destruct H0.
split; auto.
simpl.
split3; auto.
destruct (age1_juicy_mem_unpack _ _ H).
rewrite <- H3.
econstructor; eauto.
eapply eval_expr_relate; auto. destruct TC'; eassumption. auto.
apply age1_resource_decay; auto.
apply age_level; auto.

split.
2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.

assert (app_pred (|>  (F rho * P rho)) (m_phi jm)).
rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto.
assert (laterR (m_phi jm) (m_phi jm')).
constructor 1.
destruct (age1_juicy_mem_unpack _ _ H); auto.
specialize (H2 _ H3).
eapply sepcon_derives; try  apply H2; auto.
clear - Hcl Hge.
rewrite <- map_ptree_rel. 
specialize (Hcl rho (Map.set id (eval_expr e rho) (make_tenv tx))).
rewrite <- Hcl; auto.
intros.
destruct (eq_dec id i).
subst.
left; hnf; auto.
right.
rewrite Map.gso; auto. subst; auto.
apply exp_right with (eval_id id rho).
rewrite <- map_ptree_rel.
assert (env_set
         (mkEnviron (ge_of rho) (ve_of rho)
            (Map.set id (eval_expr e rho) (make_tenv tx))) id (eval_id id rho) = rho).
  unfold env_set; 
  f_equal.
  unfold eval_id; simpl.
  rewrite Map.override.
  rewrite Map.override_same. subst; auto.
  rewrite Hge in TC'. 
  destruct TC' as [TC' _]; apply typecheck_environ_sound in TC'.  
  destruct TC' as [TC' _]. unfold tc_te_denote in *.
  simpl in TC2. unfold typecheck_temp_id in *. remember ((temp_types Delta) ! id).
  destruct o; [ | inv TC2]. symmetry in Heqo. destruct p.
  specialize (TC' _ _ _ Heqo). destruct TC'. destruct H4. rewrite H4. simpl.
  f_equal. rewrite Hge; simpl. rewrite H4. reflexivity.
apply andp_right.
intros ? _. simpl.
unfold subst.
rewrite H4.
unfold eval_id at 1. unfold force_val; simpl.
rewrite Map.gss. auto.
unfold subst; rewrite H4.
auto.
Qed.

*)

Lemma semax_set_forward : 
forall (Delta: tycontext) (P: assert) id e,
    semax Hspec Delta 
        (fun rho => 
          |> (tc_expr Delta e rho  && (tc_temp_id id (typeof e) Delta e rho) && P rho)) 
          (Sset id e) 
        (normal_ret_assert 
          (fun rho => (EX old:val, 
                 !! (eval_id id rho =  subst id old (eval_expr e) rho) &&
                            subst id old P rho))).
Proof.
intros until e.
replace (fun rho : environ =>
   |>(tc_expr Delta e rho && tc_temp_id id (typeof e) Delta e rho &&
      P rho))
 with (fun rho : environ =>
     (|> tc_expr Delta e rho &&
      |> tc_temp_id id (typeof e) Delta e rho &&
      |> P rho))
  by (extensionality rho;  repeat rewrite later_andp; auto).
apply semax_straight_simple; auto. 
intros jm jm' ge vx tx rho k F [TC3 TC2] TC' Hcl Hge ? ?.
specialize (TC3 (m_phi jm') (age_laterR (age_jm_phi H))).
specialize (TC2 (m_phi jm') (age_laterR (age_jm_phi H))). 
exists jm', (PTree.set id (eval_expr e rho) (tx)).
econstructor.
split.
reflexivity.
split3; auto.
apply age_level; auto.
normalize in H0.
clear - TC' TC2 TC3 Hge.
simpl in *. simpl. rewrite <- map_ptree_rel.
apply guard_environ_put_te'; auto. subst; simpl in *.
unfold construct_rho in *; auto.
intros. simpl in *. unfold typecheck_temp_id in *.
rewrite H in TC2.
destruct t as [t b]; simpl in *.
rewrite tc_andp_sound in *; simpl in *. 
unfold_coerce. destruct TC2. 
unfold tc_bool in *. remember (is_neutral_cast (typeof e) t). 
destruct b0; inv H0. 
apply neutral_cast_typecheck_val with (Delta := Delta); auto. 
unfold guard_environ in *. destruct TC'; auto. 
destruct H0.
split; auto.
simpl.
split3; auto.
destruct (age1_juicy_mem_unpack _ _ H).
rewrite <- H3.
econstructor; eauto.
eapply eval_expr_relate; auto. destruct TC'; eassumption. auto.
apply age1_resource_decay; auto.
apply age_level; auto.

split.
2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.

assert (app_pred (|>  (F rho * P rho)) (m_phi jm)).
rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto.
assert (laterR (m_phi jm) (m_phi jm')).
constructor 1.
destruct (age1_juicy_mem_unpack _ _ H); auto.
specialize (H2 _ H3).
eapply sepcon_derives; try  apply H2; auto.
clear - Hcl Hge.
rewrite <- map_ptree_rel. 
specialize (Hcl rho (Map.set id (eval_expr e rho) (make_tenv tx))).
rewrite <- Hcl; auto.
intros.
destruct (eq_dec id i).
subst.
left; hnf; auto.
right.
rewrite Map.gso; auto. subst; auto.
apply exp_right with (eval_id id rho).
rewrite <- map_ptree_rel.
assert (env_set
         (mkEnviron (ge_of rho) (ve_of rho)
            (Map.set id (eval_expr e rho) (make_tenv tx))) id (eval_id id rho) = rho).
  unfold env_set; 
  f_equal.
  unfold eval_id; simpl.
  rewrite Map.override.
  rewrite Map.override_same. subst; auto.
  rewrite Hge in TC'. 
  destruct TC' as [TC' _]; apply typecheck_environ_sound in TC'.  
  destruct TC' as [TC' _]. unfold tc_te_denote in *.
  simpl in TC2. unfold typecheck_temp_id in *. remember ((temp_types Delta) ! id).
  destruct o; [ | inv TC2]. symmetry in Heqo. destruct p.
  specialize (TC' _ _ _ Heqo). destruct TC'. destruct H4. rewrite H4. simpl.
  f_equal. rewrite Hge; simpl. rewrite H4. reflexivity.
apply andp_right.
intros ? _. simpl.
unfold subst.
rewrite H4.
unfold eval_id at 1. unfold force_val; simpl.
rewrite Map.gss. auto.
unfold subst; rewrite H4.
auto.
Qed.

Lemma semax_set : 
forall (Delta: tycontext) (P: assert) id e,
    semax Hspec Delta 
        (fun rho => 
          |> (tc_expr Delta e rho  && (tc_temp_id id (typeof e) Delta e rho) && 
              subst id (eval_expr e rho) P rho))
          (Sset id e) (normal_ret_assert P).
Proof.
intros until e. 
replace (fun rho : environ =>
   |>(tc_expr Delta e rho && (tc_temp_id id (typeof e) Delta e rho) &&
      subst id (eval_expr e rho) P rho))
 with (fun rho : environ =>
     (|> tc_expr Delta e rho && 
      |> (tc_temp_id id (typeof e) Delta e rho) &&
      |> subst id (eval_expr e rho) P rho))
  by (extensionality rho;  repeat rewrite later_andp; auto).
apply semax_straight_simple. auto. 
intros jm jm' ge ve te rho k F [TC3 TC2] TC' Hcl Hge ? ?.
specialize (TC3 (m_phi jm') (age_laterR (age_jm_phi H))).
specialize (TC2 (m_phi jm') (age_laterR (age_jm_phi H))).
exists jm', (PTree.set id (eval_expr e rho) te).
econstructor.
split.
reflexivity.
split3; auto.
apply age_level; auto.
normalize in H0.
clear - TC' TC2 TC3 Hge.
unfold construct_rho in *.
simpl in *. rewrite Hge. simpl. rewrite <- Hge.
rewrite <- map_ptree_rel.  
apply guard_environ_put_te'; try rewrite <- Hge; auto. 
intros. simpl in *. unfold typecheck_temp_id in *.
rewrite H in TC2.
destruct t as [t b]; simpl in *.
rewrite tc_andp_sound in *; simpl in *. 
unfold_coerce. destruct TC2; simpl in *. 
unfold tc_bool in *. remember (is_neutral_cast (typeof e) t).
destruct b0; inv H0. 
destruct TC'. 
apply neutral_cast_typecheck_val with (Delta := Delta); auto. 
destruct H0.
split; auto.
simpl.
split3; auto.
destruct (age1_juicy_mem_unpack _ _ H).
rewrite <- H3.
econstructor; eauto. rewrite Hge in *. 
eapply eval_expr_relate; auto.
destruct TC'; eauto. auto. 
apply age1_resource_decay; auto.
apply age_level; auto.

split.
2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.

assert (app_pred (|>  (F rho * subst id (eval_expr e rho) P rho)) (m_phi jm)).
rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto.
assert (laterR (m_phi jm) (m_phi jm')).
constructor 1.
destruct (age1_juicy_mem_unpack _ _ H); auto.
specialize (H2 _ H3).
eapply sepcon_derives; try apply H2; try solve[rewrite <- map_ptree_rel; subst; auto].  
clear - Hcl Hge. 
specialize (Hcl rho  (Map.set id (eval_expr e rho) (make_tenv te))).
rewrite <- map_ptree_rel.
rewrite <- Hcl; auto.
intros.
destruct (eq_dec id i).
subst.
left; hnf; auto.
right.
rewrite Map.gso; auto. rewrite Hge. simpl. auto.

Qed.

Lemma later_sepcon2  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q,  P * |> Q |-- |> (P * Q).
Proof.
intros. apply @derives_trans with (|> P * |> Q).
apply sepcon_derives; auto. rewrite later_sepcon; auto.
Qed.
  
Lemma semax_load : 
forall (Delta: tycontext) sh id P e1 v2,
    semax Hspec Delta 
       (fun rho => |>
        (tc_lvalue Delta e1 rho  && (tc_temp_id_load id (typeof e1) Delta v2 rho) &&
          (mapsto sh (typeof e1) (eval_lvalue e1 rho) (v2 rho) * P rho)))
       (Sset id e1)
       (normal_ret_assert (fun rho => 
        EX old:val, (!!(eval_id id rho = subst id old v2 rho) &&
                         (subst id old (fun rho => mapsto sh (typeof e1) (eval_lvalue e1 rho) (v2 rho) * P rho) rho)))).
Proof.
intros until v2.  
replace (fun rho : environ => |> ((tc_lvalue Delta e1 rho && 
  tc_temp_id_load id (typeof e1) Delta v2 rho ) && 
  (mapsto sh (typeof e1) (eval_lvalue e1 rho) (v2 rho) * P rho)))
 with (fun rho : environ => 
   ( |> tc_lvalue Delta e1 rho && 
     |> tc_temp_id_load id (typeof e1) Delta v2 rho &&
     |> !!(typecheck_val (v2 rho) (typeof e1) = true) && 
     |> (umapsto sh (typeof e1) (eval_lvalue e1 rho) (v2 rho) * P rho))).
Focus 2.
extensionality rho.
repeat rewrite <- later_andp.
f_equal.
repeat rewrite andp_assoc. f_equal. f_equal.
unfold mapsto, umapsto. normalize.
apply semax_straight_simple. 
intro. apply boxy_andp; auto.
intros jm jm1 ge ve te rho k F [[TC2 TC1] TC3] TC' Hcl Hge ? ?.
specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi H))).
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi H))).
specialize (TC3 (m_phi jm1) (age_laterR (age_jm_phi H))).
destruct (eval_lvalue_relate _ _ _ _ _ e1 (m_dry jm) Hge (guard_environ_e1 _ _ _ TC')) as [b [ofs [? ?]]]; auto.
exists jm1.
exists (PTree.set id (v2 rho) (te)).
econstructor.
split.
reflexivity.
split3.
apply age_level; auto. simpl. 
rewrite <- map_ptree_rel.
apply guard_environ_put_te'. 
unfold typecheck_temp_id in *. 
unfold construct_rho in *. destruct rho; inv Hge; auto.
clear - TC1 TC2 TC3 TC' H2 Hge H0.
intros. simpl in TC1. unfold typecheck_temp_id in TC1.
rewrite H in TC1. 
destruct t as [t x].
destruct TC1 as [t0 [x0 [TC1 TC4]]].
inv TC1. 
eapply allowed_val_cast_sound; eauto. 
(* typechecking proof *)
split.
split3.
simpl.
rewrite <- (age_jm_dry H); constructor; auto.
assert (NONVOL: type_is_volatile (typeof e1) = false).
unfold typecheck_temp_id in *.
unfold tc_lvalue in TC2; simpl in TC2. apply tc_lvalue_nonvol in TC2; auto.
(* typechecking proof *)
apply Clight.eval_Elvalue with b ofs; auto.
destruct H0 as [H0 _].
assert ((|> (F rho * (umapsto sh (typeof e1) (eval_lvalue e1 rho) (v2 rho) * P rho)))%pred
       (m_phi jm)).
rewrite later_sepcon.
eapply sepcon_derives; try apply H0; auto.
specialize (H3 _ (age_laterR (age_jm_phi H))).
rewrite sepcon_comm in H3.
rewrite sepcon_assoc in H3.
destruct H3 as [m1 [m2 [? [? _]]]].
unfold umapsto in H4.
revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
rename m into ch.
rewrite H2 in H5.
assert (core_load ch  (b, Int.unsigned ofs) (v2 rho) (m_phi jm1)).
apply mapsto_core_load with (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh).
exists m1; exists m2; split3; auto.
apply Clight.deref_loc_value with ch; auto.
unfold loadv.
rewrite (age_jm_dry H).
apply core_load_load.
apply H6.
apply age1_resource_decay; auto.
apply age_level; auto.
rewrite <- map_ptree_rel.
rewrite <- (Hcl rho (Map.set id (v2 rho) (make_tenv te))).
normalize.
exists (eval_id id rho).
destruct H0.
apply later_sepcon2 in H0.
specialize (H0 _ (age_laterR (age_jm_phi H))).
split; [ |  apply pred_hereditary with (m_phi jm); auto; apply age_jm_phi; eauto].
eapply sepcon_derives; try apply H0; auto.
assert (env_set
         (mkEnviron (ge_of rho) (ve_of rho) (Map.set id (v2 rho) (make_tenv te))) id
         (eval_id id rho) = rho).
unfold env_set. simpl.
rewrite Map.override. unfold eval_id.
unfold tc_temp_id_load in TC1.  simpl in TC1.
destruct TC1 as [t0 [x0 [TC1 TC4]]].
destruct TC' as [TC' _].
unfold typecheck_environ in TC'. repeat rewrite andb_true_iff in TC'. destruct TC' as [[TC' _] _].
rewrite typecheck_te_eqv in TC'. unfold tc_te_denote in TC'.
destruct TC' as [TC' TC''].
specialize (TC' _ _ _ TC1). destruct TC'. destruct H4. rewrite H4. simpl.
rewrite Map.override_same; subst; auto.
unfold subst.
rewrite H4.
apply andp_right; auto.
intros ? ?; simpl.
unfold eval_id, force_val. simpl. rewrite Map.gss. auto.
apply sepcon_derives; auto.
unfold mapsto. apply andp_right; auto.
intros ? ?; unfold prop; auto.

intro i; destruct (eq_dec id i); [left; auto | right; rewrite Map.gso; auto].
subst. hnf. auto. subst. auto.
Qed.

Lemma res_option_core: forall r, res_option (core r) = None.
Proof.
 destruct r. rewrite core_NO; auto. rewrite core_YES; auto. rewrite core_PURE; auto.
Qed.


Lemma address_mapsto_can_store: forall jm ch v rsh b ofs v' my,
       (address_mapsto ch v rsh Share.top (b, Int.unsigned ofs) * exactly my)%pred (m_phi jm) ->
       decode_val ch (encode_val ch v') = v' ->
       exists m',
       {H: Mem.store ch (m_dry jm) b (Int.unsigned ofs) v' = Some m'|
       (address_mapsto ch v' rsh Share.top (b, Int.unsigned ofs) * exactly my)%pred 
       (m_phi (store_juicy_mem _ _ _ _ _ _ H))}.
Proof.
intros. rename H0 into DE.
destruct (mapsto_can_store ch v rsh b (Int.unsigned ofs) jm v') as [m' STORE]; auto.
eapply sepcon_derives; eauto.
exists m'.
exists STORE.
pose proof I.
destruct H as [m1 [m2 [? [? Hmy]]]].
do 3 red in Hmy.
assert (H2 := I); assert (H3 := I).
forget (Int.unsigned ofs) as i. clear ofs.
pose (f loc := if adr_range_dec (b,i) (size_chunk ch) loc
                      then YES (res_retain (m1 @ loc)) pfullshare (VAL (contents_at m' loc)) NoneP
                     else core (m_phi jm @ loc)).
assert (Vf: AV.valid (res_option oo f)).
apply VAL_valid; intros.
unfold compose, f in H4; clear f.
if_tac in H4.
2: rewrite res_option_core in H4; inv H4.
simpl in H4. injection H4; intros.  subst k; auto.
destruct (make_rmap _ Vf (level jm)) as [mf [? ?]]; clear Vf.
unfold f, compose; clear f; extensionality loc.
symmetry. if_tac.
unfold resource_fmap. rewrite preds_fmap_NoneP.
reflexivity.
generalize (resource_at_approx (m_phi jm) loc); 
destruct (m_phi jm @ loc); [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; try reflexivity.
auto.

unfold f in H5; clear f.
exists mf; exists m2; split3; auto.
apply resource_at_join2.
rewrite H4. symmetry. apply (level_store_juicy_mem _ _ _ _ _ _ STORE).
apply join_level in H; destruct H.
change R.rmap with rmap in *. change R.ag_rmap with ag_rmap in *.
rewrite H6; symmetry. apply (level_store_juicy_mem _ _ _ _ _ _ STORE).
intro; rewrite H5. clear mf H4 H5.
simpl m_phi.
apply (resource_at_join _ _ _ loc) in H.
destruct H1 as [vl [? ?]]. spec H4 loc. hnf in H4.
if_tac.
destruct H4. hnf in H4. rewrite H4 in H.
rewrite (proof_irr x top_share_nonunit) in H.
generalize (YES_join_full _ _ _ _ _ H); intros [rsh' ?].
rewrite H6.
unfold inflate_store; simpl.
rewrite resource_at_make_rmap.
rewrite H6 in H.
inversion H; clear H.
subst rsh1 rsh2 k sh p.
constructor.
rewrite H4; simpl.
auto.
apply join_unit1_e in H; auto.
rewrite H.
unfold inflate_store; simpl.
rewrite resource_at_make_rmap.
rewrite resource_at_approx.
case_eq (m_phi jm @ loc); simpl; intros.
rewrite core_NO. constructor. apply join_unit1; auto.
destruct k; try solve [rewrite core_YES; constructor; apply join_unit1; auto].
rewrite core_YES.
destruct (juicy_mem_contents _ _ _ _ _ _ H6). subst p0.
pose proof (store_phi_elsewhere_eq _ _ _ _ _ _ STORE _ _ _ _ H5 H6).
rewrite H8.
constructor.
apply join_unit1; auto.
rewrite core_PURE; constructor.

unfold address_mapsto in *.
exists (encode_val ch v').
destruct H1 as [vl [[? [? ?]] ?]].
split.
split3; auto.
apply encode_val_length.
intro loc. hnf.
if_tac. exists top_share_nonunit.
hnf; rewrite H5.
rewrite if_true; auto.
assert (STORE' := Mem.store_mem_contents _ _ _ _ _ _ STORE).
pose proof (juicy_mem_contents (store_juicy_mem jm m' ch b i v' STORE)).
pose proof (juicy_mem_access (store_juicy_mem jm m' ch b i v' STORE)).
pose proof (juicy_mem_max_access (store_juicy_mem jm m' ch b i v' STORE)).
pose proof I.
unfold contents_cohere in H10.
rewrite preds_fmap_NoneP.
f_equal.
specialize (H8 loc). rewrite jam_true in H8 by auto.
destruct H8. hnf in H8. rewrite H8. simpl; auto.
f_equal.
clear - STORE H9.
destruct loc as [b' z].
destruct H9.
subst b'.
rewrite (nth_getN m' b _ _ _ H0).
simpl.
f_equal.
rewrite (store_mem_contents _ _ _ _ _ _ STORE).
rewrite ZMap.gss.
replace (nat_of_Z (size_chunk ch)) with (size_chunk_nat ch) by (destruct ch; simpl; auto).
rewrite <- (encode_val_length ch v').
apply getN_setN_same.
generalize (size_chunk_pos ch); omega.
do 3 red. rewrite H5. rewrite if_false by auto.
apply core_identity.
Qed.

Ltac dec_enc :=
match goal with 
[ |- decode_val ?CH _ = ?V] => assert (DE := decode_encode_val_general V CH CH);
                               apply decode_encode_val_similar in DE; auto
end.


Lemma semax_store:
 forall Delta e1 e2 sh P, 
   typecheck_store e1 ->
   writable_share sh ->
   semax Hspec Delta 
          (fun rho =>
          |> (tc_lvalue Delta e1 rho && tc_expr Delta (Ecast e2 (typeof e1)) rho  && 
             (mapsto_ sh (typeof e1) (eval_lvalue e1 rho) * P rho)))
          (Sassign e1 e2) 
          (normal_ret_assert (fun rho => mapsto sh (typeof e1) (eval_lvalue e1 rho) ((force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1)))) * P rho)).
Proof.
intros until P. intros TC WS.
apply semax_pre with
  (fun rho : environ =>
   EX v3: val, 
      |> tc_lvalue Delta e1 rho && |> tc_expr Delta (Ecast e2 (typeof e1)) rho &&
      |> (umapsto sh (typeof e1) (eval_lvalue e1 rho) v3 * P rho)).
intro. apply andp_left2. 
unfold mapsto_. normalize. rewrite later_ex; [ | apply Vundef].
apply exp_derives; intro v3. repeat rewrite later_andp; auto.
apply extract_exists_pre; intro v3.
apply semax_straight_simple; auto.
intros jm jm1 ge ve te rho k F [TC1 TC2] TC4 Hcl Hge Hage [H0 H0'].
specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
simpl in TC2. 
rewrite tc_andp_sound in *; simpl in TC2; unfold_coerce. 
destruct TC2 as [TC2 TC3].
apply later_sepcon2 in H0.
specialize (H0 _ (age_laterR (age_jm_phi Hage))).
pose proof I.
destruct H0 as [?w [?w [? [? [?w [?w [H3 [H4 H5]]]]]]]].
unfold umapsto in H4.
revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
rename H2 into Hmode. rename m into ch.
destruct (eval_lvalue_relate _ _ _ _ _ e1 (m_dry jm) Hge (guard_environ_e1 _ _ _ TC4)) as [b0 [i [He1 He1']]]; auto.
rewrite He1' in *.
destruct (join_assoc H3 (join_comm H0)) as [?w [H6 H7]].
rewrite writable_share_right in H4 by auto.

assert (H11': (res_predicates.address_mapsto ch v3 (Share.unrel Share.Lsh sh) Share.top
        (b0, Int.unsigned i) * TT)%pred (m_phi jm1))
 by (exists w1; exists w3; split3; auto).
assert (H11: (res_predicates.address_mapsto ch v3  (Share.unrel Share.Lsh sh) Share.top
        (b0, Int.unsigned i) * exactly w3)%pred (m_phi jm1)).
generalize (address_mapsto_precise ch v3 (Share.unrel Share.Lsh sh) Share.top (b0,Int.unsigned i)); unfold precise; intro.
destruct H11' as [m7 [m8 [? [? _]]]].
specialize (H2 (m_phi jm1) _ _ H4 H9).
spec H2; [ eauto with typeclass_instances| ].
spec H2; [ eauto with typeclass_instances | ].
subst m7.
exists w1; exists w3; split3; auto. hnf. apply necR_refl.
apply address_mapsto_can_store with (v':=((force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1))))) in H11.
Focus 2.

clear - WS TC2 TC4 TC3 TC TC1 Hmode.
unfold typecheck_store in *.
destruct TC4 as [TC4 _].
destruct TC as [IT FT].
simpl in TC2. apply typecheck_expr_sound in TC2; auto.
remember (eval_expr e2 rho). remember (typeof e1). remember (typeof e2). 
destruct v; try solve [simpl in *; congruence]; destruct t; destruct t0; intuition;
try inv H; try inv Hmode; dec_enc. 
clear DE.
unfold Cop.sem_cast. simpl in *. unfold_coerce.
Transparent Float.intoffloat.
unfold Float.intoffloat.
destruct TC3. unfold_tc_denote. rewrite <- Heqv in *.
destruct (Float.Zoffloat f); try contradiction.
rewrite H. rewrite Zle_bool_rev. rewrite H0. simpl in *.
dec_enc.
Opaque Float.intoffloat.

destruct H11 as [m' [H11 AM]].
exists (store_juicy_mem _ _ _ _ _ _ H11).
exists (te);  exists rho; split3; auto.
subst; simpl; auto.
rewrite level_store_juicy_mem. apply age_level; auto.
split; auto.
split.
split3; auto.
generalize (eval_expr_relate _ _ _ _ _ e2 (m_dry jm) Hge (guard_environ_e1 _ _ _ TC4)); intro.
econstructor; try eassumption. 
unfold tc_lvalue in TC1. simpl in TC1. 
apply tc_lvalue_nonvol in TC1. auto.  (* typechecking proof *)
instantiate (1:= eval_expr e2 rho).
auto.
instantiate (1:=(force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1)))).
eapply cast_exists; eauto. destruct TC4; auto.
eapply Clight.assign_loc_value.
apply Hmode.
unfold tc_lvalue in TC1. simpl in TC1. 
apply tc_lvalue_nonvol in TC1. auto. (* typechecking proof *)
unfold Mem.storev.
simpl m_dry.
rewrite (age_jm_dry Hage); auto.
apply (resource_decay_trans _ (nextblock (m_dry jm1)) _ (m_phi jm1)).
rewrite (age_jm_dry Hage); omega.
apply (age1_resource_decay _ _ Hage).
apply resource_nodecay_decay.
apply juicy_store_nodecay.
rewrite level_store_juicy_mem. apply age_level; auto.
split.
Focus 2.
rewrite corable_funassert.
replace (core  (m_phi (store_juicy_mem _ _ _ _ _ _ H11))) with (core (m_phi jm1)).
rewrite <- corable_funassert.
eapply pred_hereditary; eauto. apply age_jm_phi; auto.
symmetry.
forget (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1))) as v.
apply rmap_ext.
do 2 rewrite level_core.
rewrite <- level_juice_level_phi; rewrite level_store_juicy_mem.
reflexivity.
intro loc.
unfold store_juicy_mem.
simpl. rewrite <- core_resource_at. unfold inflate_store. simpl.
rewrite resource_at_make_rmap. rewrite <- core_resource_at.
 case_eq (m_phi jm1 @ loc); intros; auto.
 destruct k0; simpl; repeat rewrite core_YES; auto.
rewrite sepcon_comm.
rewrite sepcon_assoc.
eapply sepcon_derives; try apply AM; auto.
unfold mapsto, umapsto.
apply andp_right. intros ? ?; unfold prop. simpl.
destruct TC4 as [TC4 _].
clear - Hmode TC3 TC2 TC4.
eapply typecheck_val_eval_cast; eauto.

rewrite Hmode.
rewrite He1'.
rewrite writable_share_right; auto.
clear - H6 H5 H1.
intros ? ?.
do 3 red in H.
destruct (nec_join2 H6 H) as [w2' [w' [? [? ?]]]].
exists w2'; exists w'; split3; auto; eapply pred_nec_hereditary; eauto.
Qed.

End extensions.
