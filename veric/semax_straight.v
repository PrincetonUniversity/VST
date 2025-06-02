Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.lifting_expr.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.semax_conseq.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.binop_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.valid_pointer.
Import LiftNotation.

Transparent intsize_eq.

Section extensions.
  Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs}.

Lemma closed_wrt_modvars_set : forall F id e v rho
  (Hclosed : closed_wrt_modvars(Σ:=Σ) (Sset id e) F),
  F rho ⊣⊢ F (mkEnviron (ge_of rho) (ve_of rho) (<[id := v]> (te_of rho))).
Proof.
  intros.
  apply Hclosed; intros.
  destruct (eq_dec i id).
  - rewrite /modifiedvars /modifiedvars' /insert_idset.
    subst; rewrite Maps.PTree.gss /=; auto.
  - rewrite lookup_insert_ne //; auto.
Qed.

Lemma semax_ptr_compare:
forall E (Delta: tycontext) (P: assert) id cmp e1 e2 ty sh1 sh2,
    sh1 <> Share.bot -> sh2 <> Share.bot ->
    is_comparison cmp = true  ->
    eqb_type (typeof e1) int_or_ptr_type = false ->
    eqb_type (typeof e2) int_or_ptr_type = false ->
    (typecheck_tid_ptr_compare Delta id = true) ->
    semax OK_spec E Delta
        (▷ (tc_expr Delta e1 ∧ tc_expr Delta e2 ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          <absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)) ∧
          <absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2)) ∧
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (∃ old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) ∧
                            assert_of (subst id (liftx old) P))).
Proof.
  intros until sh2. intros ?? CMP NE1 NE2 TCid.
  rewrite semax_unfold; intros. destruct HGG.
  iIntros "F #?" (?? (TC' & ?)) "E Pre".
  rewrite monPred_at_later !monPred_at_and.
  iApply wp_set. iApply wp_binop_rule.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit.
  { iDestruct "Pre" as "(? & _)"; auto. }
  iIntros "E %".
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit.
  { iDestruct "Pre" as "(_ & ? & _)"; auto. }
  iIntros "E %".
  rewrite bi.and_elim_r bi.and_elim_r embed_later embed_and bi.later_and /= embed_pure.
  iDestruct "Pre" as "(>% & Pre)".
  rewrite !monPred_at_absorbingly /=.
  iApply (wp_pointer_cmp _ _ _ _ _ _ _ sh1 sh2); [done..|].
  iSplit.
  { rewrite bi.and_assoc bi.and_elim_l //. }
  iIntros (v (Hcase & Hv)).
  iNext.
  rewrite /typecheck_tid_ptr_compare in TCid; destruct (temp_types Delta !! id) eqn: Hi; last done.
  iDestruct (curr_env_set_temp with "E") as "($ & E)"; [done..|].
  iIntros "Hid !>"; iSpecialize ("E" with "Hid"); iFrame.
  rewrite !bi.and_elim_r.
  assert (v = force_val2 (sem_cmp (op_to_cmp cmp) (typeof e1) (typeof e2)) (eval_expr(CS := CS) e1 rho) (eval_expr(CS := CS) e2 rho)) as Hv'.
  { rewrite /sem_cmp NE1 NE2 Hcase /= Hv //. }
  iSplit.
  - iClear "#"; iStopProof; split => n; monPred.unseal.
    unfold_lift.
    apply TC in Hi as (? & ? & ?).
    iIntros "?"; iExists (eval_id id rho); erewrite !subst_set by done.
    iSplit; last done; iPureIntro.
    rewrite eval_id_same /sem_binary_operation'.
    subst; destruct cmp; done.
  - iPureIntro.
    destruct TS as (TS & _); specialize (TS id). rewrite Hi in TS.
    destruct (temp_types Delta' !! id) eqn: ?; inv TS.
    eapply guard_environ_put_te'; eauto; first by split.
    apply tc_val'_sem_cmp; auto.
Qed.

Lemma semax_set_forward:
forall E (Delta: tycontext) (P: assert) id e,
    semax OK_spec E Delta
        (▷ (tc_expr Delta e ∧ (tc_temp_id id (typeof e) Delta e) ∧ P))
          (Sset id e)
        (normal_ret_assert
          (∃ old:val,
                 local (fun rho => eval_id id rho = subst id (liftx old) (eval_expr e) rho) ∧
                            assert_of (subst id (`old) P))).
Proof.
  intros.
  rewrite semax_unfold; intros. destruct HGG.
  iIntros "? #?" (?? (TC' & ?)) "E Pre".
  rewrite monPred_at_later !monPred_at_and.
  iApply wp_set.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit.
  { iDestruct "Pre" as "(? & _)"; auto. }
  iIntros "E % !>".
  rewrite /tc_temp_id /typecheck_temp_id /=.
  destruct (temp_types Delta !! id) eqn: Ht; last by iDestruct "Pre" as "(_ & % & _)".
  iDestruct (curr_env_set_temp with "E") as "($ & E)"; [done..|].
  iIntros "Hid !>"; iSpecialize ("E" with "Hid"); iFrame.
  iSplit.
  - iClear "#"; iStopProof; split => n; monPred.unseal.
    apply TC in Ht as (? & ? & ?).
    unfold_lift.
    iIntros "?"; iExists (eval_id id rho); erewrite !subst_set by done.
    rewrite !bi.and_elim_r eval_id_same; auto.
  - rewrite !denote_tc_assert_andp tc_bool_e.
    iAssert ⌜is_neutral_cast (implicit_deref (typeof e)) t = true⌝ with "[Pre]" as %?.
    { iDestruct "Pre" as "(_ & (? & _) & _)"; by rewrite embed_pure. }
    rewrite bi.and_elim_l; iDestruct (neutral_cast_tc_val with "Pre") as %?; [done..|].
    iPureIntro.
    destruct TS as (TS & _); specialize (TS id). rewrite Ht in TS.
    destruct (temp_types Delta' !! id) eqn: ?; inv TS.
    eapply guard_environ_put_te'; eauto; first by split.
    by apply tc_val_tc_val'.
Qed.

Lemma semax_set_forward':
forall E (Delta: tycontext) (P: assert) id e t,
    typeof_temp Delta id = Some t ->
    is_neutral_cast (typeof e) t = true ->
    semax OK_spec E Delta
        (▷ (tc_expr Delta e ∧ P))
          (Sset id e)
        (normal_ret_assert
          (∃ old:val,
                 local (fun rho => eval_id id rho = subst id (liftx old) (eval_expr e) rho) ∧
                            assert_of (subst id (`old) P))).
Proof.
intros.
eapply semax_pre, semax_set_forward.
iIntros "[TC H] !>".
iSplit; first iDestruct "H" as "[$ _]".
iSplit; last iDestruct "H" as "[_ $]".
rewrite /tc_temp_id /typecheck_temp_id /=.
unfold typeof_temp in H.
destruct (temp_types Delta !! id) eqn: Ht; inv H.
iStopProof; monPred.unseal; split => rho.
setoid_rewrite denote_tc_assert_andp.
assert (implicit_deref (typeof e) = typeof e) as -> by (by destruct (typeof e)).
rewrite H0; iIntros "?"; iSplit; auto.
by iApply (neutral_isCastResultType with "[$]").
Qed.

Lemma semax_cast_set:
forall E (Delta: tycontext) (P: assert) id e t
    (H99 : typeof_temp Delta id = Some t),
    semax OK_spec E Delta
        (▷ (tc_expr Delta (Ecast e t) ∧ P))
          (Sset id (Ecast e t))
        (normal_ret_assert
          (∃ old:val,
                 local (fun rho => eval_id id rho = subst id (liftx old) (eval_expr (Ecast e t)) rho) ∧
                            assert_of (subst id (`old) P))).
Proof.
  intros.
  rewrite semax_unfold; intros. destruct HGG.
  iIntros "? #?" (?? (TC' & ?)) "E Pre".
  rewrite monPred_at_later !monPred_at_and.
  iApply wp_set.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit.
  { iDestruct "Pre" as "(? & _)"; auto. }
  iIntros "E % !>".
  rewrite /typeof_temp in H99; destruct (temp_types Delta !! id) as [t'|] eqn: Ht; inversion H99; subst t'; clear H99.
  iDestruct (curr_env_set_temp with "E") as "($ & E)"; [done..|].
  iIntros "Hid !>"; iSpecialize ("E" with "Hid"); iFrame.
  iSplit.
  - iClear "#"; iStopProof; split => n; monPred.unseal.
    apply TC in Ht as (? & ? & ?).
    unfold_lift.
    rewrite -(bi.exist_intro (eval_id id rho)); erewrite !subst_set by done.
    rewrite !bi.and_elim_r eval_id_same; auto.
  - rewrite /tc_expr /= typecheck_cast_sound //.
    iDestruct "Pre" as "(% & _)".
    iPureIntro.
    destruct TS as (TS & _); specialize (TS id). rewrite Ht in TS.
    destruct (temp_types Delta' !! id) eqn: ?; inv TS.
    eapply guard_environ_put_te'; eauto; first by split.
    by apply tc_val_tc_val'.
    { by apply typecheck_expr_sound. }
Qed.

Lemma eval_cast_Vundef:
 forall t1 t2, eval_cast t1 t2 Vundef = Vundef.
Proof.
 intros.
 unfold eval_cast, sem_cast, classify_cast.
 destruct (eqb_type t1 int_or_ptr_type);
 destruct (eqb_type t2 int_or_ptr_type);
 destruct t1,t2;
 try destruct i; try destruct s; try destruct f;
 try destruct i0; try destruct s0; try destruct f0;
 reflexivity.
Qed.

Lemma semax_load:
forall E (Delta: tycontext) sh id (P: assert) e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
   (local (typecheck_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax OK_spec E Delta
       (▷
        (tc_lvalue Delta e1
        ∧ (⌜tc_val (typeof e1) v2⌝ ∧ P)))
       (Sset id e1)
       (normal_ret_assert (
        ∃ old:val, (local (fun rho => eval_id id rho = v2) ∧
                         assert_of (subst id (`old) P)))).
Proof.
  intros until v2.
  intros Hid0 TC1 H_READABLE H99.
  rewrite semax_unfold; intros; iIntros "F #?" (?? (TC' & ?)) "E Pre"; destruct HGG.
  rewrite monPred_at_later !monPred_at_and monPred_at_pure.
  iApply wp_set.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  rewrite bi.and_comm -assoc bi.later_and; iDestruct "Pre" as "(>%Htc2 & Pre)".
  iApply wp_expr_mapsto; iApply (wp_tc_lvalue(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite bi.and_elim_r; auto.
  iIntros "E" (b o Hbo).
  iExists sh, v2; iSplit.
  { iPureIntro; split; first done. intros ->; eapply tc_val_Vundef; eauto. }
  iSplit.
  { eapply monPred_in_entails in H99.
    iNext; iPoseProof (H99 with "[Pre]") as "H".
    { rewrite bi.and_elim_l monPred_at_and; iFrame; auto. }
    rewrite monPred_at_absorbingly /=; unfold_lift.
    by rewrite Hbo. }
  iNext.
  rewrite /typeof_temp in Hid0; destruct (temp_types Delta !! id) as [t'|] eqn: Ht; inversion Hid0; subst t'; clear Hid0.
  iDestruct (curr_env_set_temp with "E") as "($ & E)"; [done..|].
  iIntros "Hid !>"; iSpecialize ("E" with "Hid"); iFrame.
  simpl; iSplit.
  - iClear "#"; iStopProof; split => n; monPred.unseal.
    apply TC in Ht as (? & ? & ?).
    unfold_lift.
    rewrite -(bi.exist_intro (eval_id id rho)); erewrite !subst_set by done.
    rewrite eval_id_same bi.and_elim_l; auto.
  - iPureIntro.
    destruct TS as (TS & _); specialize (TS id). rewrite Ht in TS.
    destruct (temp_types Delta' !! id) eqn: ?; inv TS.
    eapply guard_environ_put_te'; eauto; first by split.
    eapply tc_val_tc_val', neutral_cast_subsumption; eauto.
Qed.

Lemma mapsto_tc' : forall sh t p v, mapsto sh t p v ⊢ ⌜tc_val' t v⌝.
Proof.
  intros; rewrite /mapsto.
  iIntros "H".
  destruct (access_mode t); try done.
  destruct (type_is_volatile t); try done.
  destruct p; try done.
  if_tac.
  - iDestruct "H" as "[(% & _) | (% & _)]"; iPureIntro; by [apply tc_val_tc_val' | subst; apply tc_val'_Vundef].
  - iDestruct "H" as "(($ & _) & _)".
Qed.

Lemma mapsto_tc : forall sh t p v, v <> Vundef -> mapsto sh t p v ⊢ ⌜tc_val t v⌝.
Proof.
  intros; rewrite mapsto_tc'; iPureIntro.
  by intros X; apply X.
Qed.

Lemma semax_cast_load:
forall E (Delta: tycontext) sh id (P: assert) e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
   (local (typecheck_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax OK_spec E Delta
       (▷
        (tc_lvalue Delta e1
        ∧ local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2)))
        ∧ P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (
        ∃ old:val, local (fun rho => eval_id id rho = (`(eval_cast (typeof e1) t1 v2)) rho) ∧
                         assert_of (subst id (`old) P))).
Proof.
  intros until v2.
  intros Hid0 HCAST H_READABLE H99.
  rewrite semax_unfold; intros; iIntros "F #?" (?? (TC' & ?)) "E Pre"; destruct HGG.
  rewrite monPred_at_later !monPred_at_and.
  iApply wp_set; iApply wp_cast; first done.
  iApply wp_expr_mono; first by intros; iIntros "H"; iApply "H".
  iApply wp_expr_mapsto.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  destruct (eq_dec v2 Vundef).
  { subst; iAssert (▷ False) with "[Pre]" as ">[]".
    iNext; rewrite bi.and_elim_r bi.and_elim_l eval_cast_Vundef.
    iDestruct "Pre" as %[]%tc_val_Vundef. }
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  eapply monPred_in_entails in H99.
  iDestruct (add_and _ (▷ ⌜tc_val (typeof e1) v2⌝) with "Pre") as "(Pre & >%)".
  { iIntros "(_ & _ & H) !>"; iPoseProof (H99 with "[H]") as "H"; auto.
    { rewrite monPred_at_and; iFrame; auto. }
    rewrite monPred_at_absorbingly embed_absorbingly; iMod "H".
    by iDestruct (mapsto_tc with "H") as %?. }
  iApply (wp_tc_lvalue(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite !bi.and_elim_l; auto.
  iIntros "E" (b o Hbo).
  iExists sh, v2; iSplit; first done.
  iSplit.
  { iNext; iPoseProof (H99 with "[Pre]") as "H".
    { rewrite !bi.and_elim_r monPred_at_and; iFrame; auto. }
    rewrite monPred_at_absorbingly /=; unfold_lift; by rewrite Hbo. }
  rewrite bi.and_comm -assoc bi.later_and; iDestruct "Pre" as "(>%Htc & Pre)".
  iIntros "!>"; iSplit; first done.
  unfold eval_cast, force_val1 in Htc.
  destruct (sem_cast (typeof e1) t1 v2) as [v|] eqn: Hcast; last by apply tc_val_Vundef in Htc.
  iExists v; iSplit; first done; iNext.
  rewrite /typeof_temp in Hid0; destruct (temp_types Delta !! id) as [t'|] eqn: Ht; inversion Hid0; subst t'; clear Hid0.
  iDestruct (curr_env_set_temp with "E") as "($ & E)"; [done..|].
  iIntros "Hid !>"; iSpecialize ("E" with "Hid"); iFrame.
  simpl; iSplit.
  - iClear "#"; iStopProof; split => ?; monPred.unseal.
    apply TC in Ht as (? & ? & ?).
    unfold_lift.
    rewrite -(bi.exist_intro (eval_id id rho)); erewrite !subst_set by done.
    rewrite eval_id_same bi.and_elim_l Hcast; auto.
  - iPureIntro.
    destruct TS as (TS & _); specialize (TS id). rewrite Ht in TS.
    destruct (temp_types Delta' !! id) eqn: ?; inv TS.
    eapply guard_environ_put_te'; eauto; first by split.
    by apply tc_val_tc_val'.
Qed.

Lemma writable0_lub_retainer_Rsh:
 forall sh, writable0_share sh ->
  Share.lub (retainer_part sh) Share.Rsh = sh.
  intros. symmetry.
  unfold retainer_part.
  rewrite -> (comp_parts comp_Lsh_Rsh sh) at 1.
  f_equal; auto.
  unfold writable0_share in H.
  apply leq_join_sub in H.  apply Share.ord_spec1 in H. auto.
Qed.

Theorem load_store_similar':
   forall (chunk : memory_chunk) (m1 : Memory.mem)
         (b : Values.block) (ofs : Z) (v : val) (m2 : Memory.mem),
       store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  (align_chunk chunk' | ofs) ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk' b ofs).
  split; auto.
  destruct (store_valid_access_1 _ _ _ _ _ _ H _ _ _ _ (store_valid_access_3 _ _ _ _ _ _ H)).
  rewrite H0.
  eapply range_perm_implies; eauto. constructor.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B.
  rewrite (store_mem_contents _ _ _ _ _ _ H).
  rewrite Maps.PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H0.
  apply Nat2Z.inj; auto.
Qed.

Lemma semax_store:
 forall E Delta e1 e2 sh P (WS : writable0_share sh),
   semax OK_spec E Delta
          (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ P)))
          (Sassign e1 e2)
          (normal_ret_assert (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) ∗ P)).
Proof.
  intros.
  rewrite semax_unfold; intros; iIntros "? #?" (?? (TC' & ?)) "E Pre"; destruct HGG.
  rewrite monPred_at_later !monPred_at_and.
  iApply wp_store.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite bi.and_elim_l bi.and_elim_r; auto.
  iIntros "E" (?).
  iSplit; first by iPureIntro; apply tc_val_tc_val'.
  iApply (wp_tc_lvalue(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite !bi.and_elim_l; auto.
  iIntros "E" (?? Hbo).
  iExists _; iSplit; first done.
  rewrite !monPred_at_sep.
  iDestruct "Pre" as "(_ & He1 & P)"; iSplitL "He1".
  { simpl; unfold_lift; rewrite Hbo; auto. }
  iNext; iIntros "He1 !>"; simpl; iFrame.
  iSplit; last done.
  rewrite monPred_at_sep /=; iFrame; unfold_lift.
  rewrite Hbo; done.
Qed.

Lemma semax_store_union_hack:
     forall
         E (Delta : tycontext) (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : assert),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax OK_spec E Delta
         (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
              ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1)))
               ∗ P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (∃ v':val,
              (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) ∧
              (assert_of ((` (mapsto sh t2)) (eval_lvalue e1) (`v')) ∗ P))).
Proof.
  intros until P. intros NT AM0 AM' OK WS.
  assert (SZ := decode_encode_val_size _ _ OK).
  rewrite semax_unfold; intros; iIntros "? #?" (?? (TC' & ?)) "E Pre"; destruct HGG.
  rewrite monPred_at_later !monPred_at_and.
  iApply wp_store'; [done..|].
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite bi.and_elim_l bi.and_elim_r; auto.
  iIntros "E" (?).
  iSplit; first by iPureIntro; apply tc_val_tc_val'.
  iApply (wp_tc_lvalue(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite !bi.and_elim_l; auto.
  iIntros "E" (?? Hbo).
  iExists _; iSplit; first by iPureIntro; apply writable_writable0.
  rewrite !monPred_at_sep !monPred_at_and.
  iDestruct "Pre" as "(_ & He1 & P)"; iSplitL "He1".
  { simpl; unfold_lift; rewrite Hbo; auto. }
  iNext; iIntros "(% & % & He1) !>"; simpl; iFrame.
  iSplit; last done.
  rewrite monPred_at_exist; iExists v'.
  rewrite -Hbo monPred_at_and monPred_at_sep; iFrame; auto.
Qed.

End extensions.
