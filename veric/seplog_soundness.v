Require Import veric.base.
Require Import msl.normalize.
Require Import veric.Address.
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
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.

Open Local Scope pred.

Section extensions.
Context {Z} (Hspec: juicy_ext_spec Z).

Lemma semax_straight_simple:
 forall Delta G (B: assert) P c Q,
  (forall rho, boxy extendM (B rho)) ->
  some_static_thing Delta c -> 
  (forall jm jm1 ge rho k F, 
              app_pred (B rho) (m_phi jm) ->
              typecheck_environ rho Delta = true ->
              closed_wrt_modvars c F ->
              filter_genv ge = ge_of rho ->
              age jm jm1 ->
              ((F rho * |>P rho) && funassert G rho) (m_phi jm) ->
              exists jm', exists te', exists rho',
                rho' = mkEnviron (ge_of rho) (ve_of rho) te' /\
                level jm = S (level jm') /\
                typecheck_environ rho' Delta = true /\
                jstep cl_core_sem ge (State (ve_of rho) (te_of rho) (Kseq c :: k)) jm 
                                 (State (ve_of rho') (te_of rho') k) jm' /\
              ((F rho' * Q rho') && funassert G rho) (m_phi jm')) ->
  semax Hspec Delta G (fun rho => B rho && |> P rho) c (normal_ret_assert Q).
Proof.
intros until Q; intros EB TC Hc.
rewrite semax_unfold.
split.
auto.
intros psi n _ k F Hcl Hsafe rho w Hx w0 H Hglob.
apply nec_nat in Hx.
apply (pred_nec_hereditary _ _ _ Hx) in Hsafe.
clear n Hx.
apply (pred_nec_hereditary _ _ _ (necR_nat H)) in Hsafe.
clear H w.
rename w0 into w.
apply assert_safe_last'; intro Hage.
intros ora jm H2. subst w.
rewrite andp_assoc in Hglob.
destruct Hglob as [[TC' Hge] Hglob].
apply can_age_jm in Hage; destruct Hage as [jm1 Hage].
destruct Hglob as [Hglob Hglob'].
apply extend_sepcon_andp in Hglob; auto.
destruct Hglob as [TC2 Hglob].
specialize (Hc jm  jm1 psi rho k F TC2 TC' Hcl  Hge Hage (conj Hglob Hglob')); clear Hglob Hglob'.
destruct Hc as [jm' [te' [rho' [H9 [H2 [TC'' [H3 H4]]]]]]].
change (@level rmap _  (m_phi jm) = S (level (m_phi jm'))) in H2.
rewrite H2 in Hsafe.
eapply safe_step'_back2; [eassumption | ].
specialize (Hsafe EK_normal nil rho').
simpl exit_cont in Hsafe.
specialize (Hsafe (m_phi jm')).
spec Hsafe.
change R.rmap with rmap; omega.
specialize (Hsafe _ (necR_refl _)).
spec Hsafe.
split; auto.
split; auto.
subst rho'; auto.
destruct H4; split; auto.
subst rho'.
unfold normal_ret_assert.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
auto.
subst rho'.
destruct rho; simpl in *; auto.
hnf in Hsafe.
change R.rmap with rmap in *.
replace (@level rmap ag_rmap (m_phi jm) - 1)%nat with (@level rmap ag_rmap (m_phi jm'))%nat by omega.
apply Hsafe; auto.
Qed.


Lemma semax_set : 
forall (Delta: tycontext) (G: funspecs) (P: assert) id e,
    semax Hspec Delta G 
        (fun rho => 
          !!(typecheck_temp_id id (typeof e) Delta = true) &&
           tc_expr Delta e rho  && 
            |> subst id (eval_expr rho e) P rho)
          (Sset id e) (normal_ret_assert P).
Proof.

intros until e.
apply semax_straight_simple.
 admit. (* auto.*)
apply prove_some_static_thing.
intros jm jm' ge rho k F [TC2 TC3] TC' Hcl Hge ? ?.
exists jm', (PTree.set id (eval_expr rho e) (te_of rho)).
econstructor.
split.
reflexivity.
split3; auto.
apply age_level; auto.
normalize in H0.
clear - TC' TC2 TC3.
apply typecheck_environ_put_te; auto.
intros. simpl in *. unfold typecheck_temp_id in *.
rewrite H in TC2.
destruct t as [t b]; simpl in *.
rewrite eqb_type_eq in TC2; apply type_eq_true in TC2. subst t.
apply typecheck_expr_sound in TC3; auto.
destruct H0.
split; auto.
simpl.
split3; auto.
destruct (age1_juicy_mem_unpack _ _ H).
rewrite <- H3.
econstructor; eauto.
eapply eval_expr_relate; eauto.
apply age1_resource_decay; auto.
apply age_level; auto.

split.
2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.

assert (app_pred (|>  (F rho * subst id (eval_expr rho e) P rho)) (m_phi jm)).
rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto.
assert (laterR (m_phi jm) (m_phi jm')).
constructor 1.
destruct (age1_juicy_mem_unpack _ _ H); auto.
specialize (H2 _ H3).
eapply sepcon_derives; try  apply H2; auto.
clear - Hcl.
specialize (Hcl rho  (PTree.set id (eval_expr rho e) (te_of rho))).
rewrite <- Hcl; auto.
intros.
destruct (eq_dec id i).
subst.
left; hnf; auto.
right.
rewrite PTree.gso; auto.
Qed.

Lemma later_sepcon2  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q,  P * |> Q |-- |> (P * Q).
Proof.
intros. apply @derives_trans with (|> P * |> Q).
apply sepcon_derives; auto. rewrite later_sepcon; auto.
Qed.

Lemma semax_load : 
forall (Delta: tycontext) (G: funspecs) sh id P e1 v2,
    lvalue_closed_wrt_vars (eq id) e1 ->
    semax Hspec Delta G 
       (fun rho =>
        !!(typecheck_temp_id id (typeof e1) Delta = true) && tc_lvalue Delta e1 rho  && 
          |> (mapsto' sh e1 v2 rho * subst id v2 P rho))
       (Sset id e1)
       (normal_ret_assert (fun rho => mapsto' sh e1 v2 rho * P rho)).
Proof.
intros until v2. intros TC3.
apply semax_straight_simple. admit. (* auto. *)
apply prove_some_static_thing.
intros jm jm1 ge rho k F [TC1 TC2] TC' Hcl Hge ? ?.
destruct (eval_lvalue_relate _ _ _ e1 (m_dry jm)  Hge TC') as [b [ofs [? ?]]]; auto.
exists jm1.
exists (PTree.set id v2 (te_of rho)).
econstructor.
split.
reflexivity.
split3.
apply age_level; auto.
apply typecheck_environ_put_te. auto.
generalize dependent v2.  
clear - TC1 TC2 TC' H2.
unfold typecheck_temp_id in *. 
intros. simpl in TC1. rewrite H in TC1. 
destruct t as [t x]. rewrite eqb_type_eq in TC1; apply type_eq_true in TC1. subst t.
simpl.
admit. (* typechecking proof, stuck, need to figure out how this works *)
split.
split3.
simpl.
rewrite <- (age_jm_dry H); constructor; auto.
assert (NONVOL: type_is_volatile (typeof e1) = false).
unfold typecheck_temp_id in *.
simpl in TC1.
revert TC1; case_eq ((temp_types Delta) ! id); intros; try discriminate.
destruct p as [t b']. rewrite eqb_type_eq in TC1; apply type_eq_true in TC1. subst t.
admit. (* typechecking proof *)
apply Clight_sem.eval_Elvalue with b ofs; auto.
destruct H0 as [H0 _].
assert ((|> (F rho * (mapsto' sh e1 v2 rho * subst id v2 P rho)))%pred
       (m_phi jm)).
rewrite later_sepcon.
eapply sepcon_derives; try apply H0; auto.
specialize (H3 _ (age_laterR (age_jm_phi H))).
rewrite sepcon_comm in H3.
rewrite sepcon_assoc in H3.
destruct H3 as [m1 [m2 [? [? _]]]].
unfold mapsto' in H4.
revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
rename m into ch.
rewrite H2 in H5.
assert (core_load ch  (b, Int.unsigned ofs) v2 (m_phi jm1)).
apply mapsto_core_load with (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh).
exists m1; exists m2; split3; auto.
apply Csem.deref_loc_value with ch; auto.
unfold loadv.
rewrite (age_jm_dry H).
apply core_load_load.
apply H6.
apply age1_resource_decay; auto.
apply age_level; auto.

rewrite <- (Hcl rho (PTree.set id v2 (te_of rho))).
unfold mapsto'.
rewrite <- (TC3 rho (PTree.set id v2 (te_of rho))).
destruct H0.
split; [ | eapply pred_hereditary; eauto; apply age_jm_phi; eauto].
apply later_sepcon2 in H0.
apply H0. do 3 red. apply age_laterR. apply age_jm_phi; auto.
intro i; destruct (eq_dec id i); [left; auto | right; rewrite PTree.gso; auto].
intro i; destruct (eq_dec id i); [left; auto | right; rewrite PTree.gso; auto].
hnf. auto.
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
rewrite <- resource_at_approx.
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



Lemma semax_store:
 forall Delta G e1 e2 v3 rsh P 
   (TC: typecheck_store e1 e2),
    typeof e1 = typeof e2 -> 
   (* admit:  make this more accepting of implicit conversions! *) 
   semax Hspec Delta G 
          (fun rho =>
          (*!!(denote_tc_assert(isCastResultType (typeof e2) (typeof e1) (typeof e1) e2) rho) &&*)
          tc_lvalue Delta e1 rho && tc_expr Delta e2 rho  && 
          |> (mapsto' (Share.splice rsh Share.top) e1 v3 rho * P rho))
          (Sassign e1 e2) 
          (normal_ret_assert (fun rho => mapsto' (Share.splice rsh Share.top) e1 (eval_expr rho e2) rho * P rho)).
Proof.
intros until P. intros TC TC3.
apply semax_straight_simple; auto.
apply prove_some_static_thing.
intros jm jm1 ge rho k F [TC1 TC2] TC4 Hcl Hge Hage [H0 H0'].
apply later_sepcon2 in H0.
specialize (H0 _ (age_laterR (age_jm_phi Hage))).
pose proof I.
destruct H0 as [?w [?w [? [? [?w [?w [H3 [H4 H5]]]]]]]].
unfold mapsto' in H4.
revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
rename H2 into Hmode. rename m into ch.
destruct (eval_lvalue_relate _ _ _ e1 (m_dry jm) Hge TC4) as [b0 [i [He1 He1']]]; auto.
rewrite He1' in *.
destruct (join_assoc H3 (join_comm H0)) as [?w [H6 H7]].
rewrite Share.unrel_splice_R in H4. rewrite Share.unrel_splice_L in H4.

assert (H11': (res_predicates.address_mapsto ch v3 rsh Share.top
        (b0, Int.unsigned i) * TT)%pred (m_phi jm1))
 by (exists w1; exists w3; split3; auto).
assert (H11: (res_predicates.address_mapsto ch v3  rsh Share.top
        (b0, Int.unsigned i) * exactly w3)%pred (m_phi jm1)).
generalize (address_mapsto_precise ch v3  rsh Share.top (b0,Int.unsigned i)); unfold precise; intro.
destruct H11' as [m7 [m8 [? [? _]]]].
specialize (H2 (m_phi jm1) _ _ H4 H9).
spec H2; [ eauto with typeclass_instances| ].
spec H2; [ eauto with typeclass_instances | ].
subst m7.
exists w1; exists w3; split3; auto. hnf. apply necR_refl.
apply address_mapsto_can_store with (v':=(eval_expr rho e2)) in H11.
Focus 2.
clear - TC2 TC4 TC3 TC  Hmode.
unfold typecheck_store in *.
destruct TC as [IT  ?].
destruct H as [FT NA].
rewrite TC3 in *; clear TC3.
simpl in TC2. apply typecheck_expr_sound in TC2; auto.
remember (eval_expr rho e2). destruct v; intuition;
remember (typeof e2); destruct t; intuition; simpl in Hmode; try congruence.
inv H.
destruct ch; try congruence; auto.
assert (decode_encode_val (Vint i) Mint32 Mint32 (decode_val Mint32 (encode_val Mint32 (Vint i)))).
apply decode_encode_val_general; auto.
apply decode_encode_val_similar in H; auto.
destruct ch; simpl in Hmode; try congruence.
assert (decode_encode_val (Vint i) Mint32 Mint32 (decode_val Mint32 (encode_val Mint32 (Vint i)))).
apply decode_encode_val_general; auto.
apply decode_encode_val_similar in H; auto.
destruct (typeof e2); try solve[simpl in *; congruence].
destruct ch; try solve[simpl in *; destruct f0; congruence].
assert (decode_encode_val (Vfloat f) Mfloat64 Mfloat64 (decode_val Mfloat64 (encode_val Mfloat64 (Vfloat f)))).
apply decode_encode_val_general; auto.
apply decode_encode_val_similar in H0; auto.
destruct (typeof e2); try solve[ simpl in *; congruence].
destruct ch; try solve[simpl in *; congruence].
assert (decode_encode_val (Vptr b i) Mint32 Mint32 (decode_val Mint32 (encode_val Mint32 (Vptr b i)))).
apply decode_encode_val_general; auto.
apply decode_encode_val_similar in H; auto. (* typechecking proof, simplified by limiting float and int types allowed for now.*)
destruct H11 as [m' [H11 AM]].
exists (store_juicy_mem _ _ _ _ _ _ H11).
exists (te_of rho);  exists rho; split3; auto.
destruct rho; simpl; auto.
rewrite level_store_juicy_mem. apply age_level; auto.
split; auto.
split.
split3; auto.
generalize (eval_expr_relate _ _ _ e2 (m_dry jm) Hge TC4); intro.
econstructor; try eassumption. 
unfold tc_lvalue in TC1. simpl in TC1. 
apply tc_lvalue_nonvol in TC1. auto.  (* typechecking proof ? *)
instantiate (1:= eval_expr rho e2).
auto.
rewrite TC3.
instantiate (1:=eval_expr rho e2).
unfold tc_expr in TC2. simpl in TC2. apply typecheck_expr_sound in TC2.
unfold sem_cast.
unfold typecheck_store in *.
destruct TC as [IT [FT NA]].
rewrite TC3 in *.
remember (typeof e2). unfold classify_cast.
destruct t; auto; simpl;
intuition; try inv H8;
try solve [simpl; destruct (eval_expr rho e2); try solve[intuition]].
destruct (eval_expr rho e2); intuition. 
unfold typecheck_store in *.
(* make this more general as a kind of typechecking proof
           Done with simplifications *)
eapply Csem.assign_loc_value.
apply Hmode.
admit. (* typechecking proof *)
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
replace (core  (m_phi (store_juicy_mem _ _ _ _ _ _ H11))) with (core (m_phi jm)).
rewrite <- corable_funassert; auto.
symmetry.
admit.  (* core_store_juicy_mem *) 
rewrite sepcon_comm.
rewrite sepcon_assoc.
eapply sepcon_derives; try apply AM; auto.
unfold mapsto'.
rewrite Hmode.
rewrite He1'.
rewrite Share.unrel_splice_R. rewrite Share.unrel_splice_L. auto.
clear - H6 H5 H1.
intros ? ?.
do 3 red in H.
destruct (nec_join2 H6 H) as [w2' [w' [? [? ?]]]].
exists w2'; exists w'; split3; auto; eapply pred_nec_hereditary; eauto.
Qed.

Lemma semax_ifthenelse : 
   forall Delta G P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax Hspec Delta G (fun rho => P rho && !! expr_true b rho) c R -> 
     semax Hspec Delta G (fun rho => P rho && !! expr_true (Cnot b) rho) d R -> 
     semax Hspec Delta G 
              (fun rho => tc_expr Delta b rho && P rho)
              (Sifthenelse b c d) R.
Proof.
intros.
rewrite semax_unfold in H0, H1 |- *.
destruct H0 as [TC0 ?].
destruct H1 as [TC1 ?].
split.
apply prove_some_static_thing.
intros.
specialize (H0 psi _ Prog_OK k F).
specialize (H1 psi _ Prog_OK k F).
spec H0. intros i te' ?.  apply H2; simpl; auto. intros i0; destruct (H4 i0); intuition. left; left; auto.
spec H1. intros i te' ?.  apply H2; simpl; auto; intros i0; destruct (H4 i0); intuition. left; right; auto.
specialize (H0 H3).
specialize (H1 H3).
clear Prog_OK H3.
intro rho; specialize (H0 rho); specialize (H1 rho).
slurp.
rewrite <- fash_and.
intros ? ?. clear w H0.
revert a'.
apply fash_derives.
intros w [? ?].
intros ?w ? [[[?TC Hge] ?] ?].
apply extend_sepcon_andp in H4; auto.
destruct H4 as [TC2 H4].
hnf in TC2.
destruct H4 as [w1 [w2 [? [? ?]]]].
specialize (H0 w0 H3).
specialize (H1 w0 H3).
unfold expr_true, Cnot in *.
intros ora jm Hphi.
generalize (eval_expr_relate _ _ _ b (m_dry jm) Hge TC); intro.
assert (exists b': bool, bool_val (eval_expr rho b) (typeof b) = Some b').
clear - TC H TC2.
assert (TCS := typecheck_expr_sound _ _ _ TC TC2).
remember (eval_expr rho b). destruct v;
simpl; destruct (typeof b); intuition; eauto. (* typechecking proof *)
destruct H9 as [b' ?].
apply wlog_safeN_gt0; intro.
subst w0.
change (level (m_phi jm)) with (level jm) in H10.
revert H10; case_eq (level jm); intros.
omegaContradiction.
apply levelS_age1 in H10. destruct H10 as [jm' ?].
clear H11.
apply (@safe_step'_back2 _ _ _ _ _ _ _ psi ora _ jm 
        (State (ve_of rho) (te_of rho) (Kseq (if b' then c else d) :: k)) jm' _).
split3.
rewrite <- (age_jm_dry H10); econstructor; eauto.
apply age1_resource_decay; auto.
apply age_level; auto.
change (level (m_phi jm)) with (level jm).
replace (level jm - 1)%nat with (level jm' ) by (apply age_level in H10; omega).
eapply @age_safe; try apply H10.
destruct b'.
eapply H0; auto.
split; auto.
split; auto.
split; auto.
rewrite andp_comm; rewrite prop_true_andp by auto.
do 2 econstructor; split3; eauto.
eapply H1; auto.
split; auto.
split; auto.
split; auto.
rewrite andp_comm; rewrite prop_true_andp.
do 2 econstructor; split3; eauto.
clear - H TC TC2 H9.
assert (TCS := typecheck_expr_sound _ _ _ TC TC2).
simpl. 
destruct (eval_expr rho b); try solve[inv H9].
destruct (typeof b); 
try solve [simpl in *; inv H9; rewrite TCS in H1; congruence].
intuition; simpl in *;
unfold sem_notbool; destruct i0; destruct s; auto; simpl;
inv H9; rewrite negb_false_iff in H1; rewrite H1; auto.
destruct (typeof b); intuition. simpl in *. inv H9.
rewrite negb_false_iff in H1. rewrite H1; auto.
destruct (typeof b); intuition. (* typechecking proof *)
Qed.


   (* Scall *)


Lemma opt2list_inj: forall A (a b: option A), opt2list a = opt2list b -> a=b.
Proof.
destruct a; destruct b; intros; inv H; auto.
Qed.


Lemma unlater_writable:
  forall m m', laterR m m' -> 
            forall loc, writable loc m' -> writable loc m.
Proof.
induction 1; intros; auto.
hnf in *.
simpl in H0.
assert (match y @ loc with
     | YES rsh sh k _ => sh = pfullshare /\ isVAL k
     | _ => False
     end) by (destruct (y @ loc); eauto).
clear H0.
revert H1; case_eq (y @ loc); intros; try contradiction.
destruct H1; subst.
destruct (rmap_unage_YES _ _ _ _ _ _ _ H H0).
rewrite H1; simpl; auto.
Qed.

Lemma age_twin' {A B} `{HA: ageable A} `{HB: ageable B}:
  forall (x: A) (y: B) (x': A),
       level x = level y -> age x x' ->
       exists y', level x' = level y' /\ age y y'.
Proof.
intros x y x' H0 H1.
unfold fashionR in *.
destruct (age1_levelS _ _ H1) as [n ?].
rewrite H0 in H.
destruct (levelS_age1 _ _ H) as [y' ?].
exists y'; split.
apply age_level in H2.
apply age_level in H1.
congruence.
auto.
Qed.

Lemma later_twin' {A B} `{HA: ageable A} `{HB: ageable B}:
  forall (x: A) (y: B) (x': A),
       level x = level y -> laterR x x' ->
       exists y', level x' = level y' /\ laterR y y'.
Proof.
intros x y x' H0 H1.
revert y H0; induction H1; intros.
destruct (age_twin' _ _ _ H0 H) as [y' [? ?]].
exists y'; split; auto.
specialize (IHclos_trans1 _ H0).
destruct IHclos_trans1 as [y2 [? ?]].
specialize (IHclos_trans2 _ H).
destruct IHclos_trans2 as [u [? ?]].
exists u; split; auto.
apply t_trans with y2; auto.
Qed.

Lemma later_twin {A} `{ageable A}:
   forall phi1 phi2 phi1',
     level phi1 = level phi2 ->
     laterR phi1 phi1' ->
     exists phi2', level phi1' = level phi2' /\ laterR phi2 phi2'.
Proof.
intros.
eapply later_twin'; eauto.
Qed.

Lemma someP_inj:  forall A P Q, SomeP A P = SomeP A Q -> P=Q.
Proof. intros. injection H; intro. apply inj_pair2 in H0. auto. Qed.

Lemma prop_unext: forall P Q: Prop, P=Q -> (P<->Q).
Proof. intros. subst; split; auto. Qed.

Lemma function_pointer_aux:
  forall A P P' Q Q' (w: rmap), 
   SomeP (A::boolT::list val::nil) (approx (level w) oo packPQ P Q) =
   SomeP (A::boolT::list val::nil) (approx (level w) oo packPQ P' Q') ->
   ( (forall x vl, (! |> (P' x vl <=> P x vl)) w) /\
     (forall x vl, (! |> (Q' x vl <=> Q x vl)) w)).
Proof.
intros.
apply someP_inj in H.
unfold packPQ, compose in H.
split; intros.
apply equal_f with (x,(true,(vl,tt))) in H.
simpl in H.
rewrite @later_fash; auto with typeclass_instances.
intros ? ? m' ?.
split; intros m'' ? ?;  apply f_equal with (f:= fun x => app_pred x m'') in H;
apply prop_unext in H; apply approx_p with (level w); apply H;
apply approx_lt; auto; clear - H0 H1 H2; hnf in H1; apply laterR_level in H1;
apply necR_level in H2; simpl in *;
change compcert_rmaps.R.ag_rmap with ag_rmap in *;
change compcert_rmaps.R.rmap with rmap in *;
omega.
apply equal_f with (x,(false,(vl,tt))) in H.
simpl in H.
rewrite @later_fash; auto with typeclass_instances; intros ? ? m' ?;
split; intros m'' ? ?;  apply f_equal with (f:= fun x => app_pred x m'') in H;
apply prop_unext in H; apply approx_p with (level w); apply H;
apply approx_lt; auto; clear - H0 H1 H2; hnf in H1; apply laterR_level in H1;
apply necR_level in H2; simpl in *;
change compcert_rmaps.R.ag_rmap with ag_rmap in *;
change compcert_rmaps.R.rmap with rmap in *; omega.
Qed.


Definition get_result (ret: option ident) (ty: type) (rho: environ) : list val :=
 match ret with None => nil | Some x => (force_val (PTree.get x (te_of rho)))::nil end.

Lemma environ_ge_ve_disjoint:
  forall rho Delta, typecheck_environ rho Delta = true ->
        forall id, ge_of rho id = None \/ PTree.get id (ve_of rho) = None.
Admitted.

Lemma semax_fun_id:
      forall id fsig (A : Type) (P' Q' : A -> list val -> pred rmap)
              Delta (G : funspecs) P Q c,
    In (id, mk_funspec fsig A P' Q') G ->
       semax Hspec Delta G (fun rho => P rho 
                                && fun_assert (eval_lvalue rho (Evar id (Tfunction (fst fsig) (snd fsig)))) fsig A P' Q')
                              c Q ->
       semax Hspec Delta G P c Q.
Proof.
intros.
rewrite semax_unfold in H0|-*.
destruct H0; split; auto.
intros.
specialize (H1 psi w Prog_OK k F H2 H3).
intros rho w' ? w'' ? ?.
apply (H1 rho w' H4 w'' H5); clear H1.
destruct H6; split; auto.
destruct H1 as [[H1 Hge] ?]; split; auto.
split; auto.
normalize.
split; auto.
assert (app_pred (believe Hspec G psi G) (level w'')).
apply pred_nec_hereditary with (level w'); eauto.
apply nec_nat; apply necR_level; auto.
apply pred_nec_hereditary with w; eauto.
apply nec_nat; auto.
hnf in H1. 
pose proof (environ_ge_ve_disjoint _ _ H1 id).
clear - H6 H8 H H9 Hge.
destruct H6 as [H6 H6'].
specialize (H6 _ _  _(necR_refl _) H).
destruct H6 as [v [loc [[? ?] ?]]].
simpl in H0, H1, H2.
destruct H9; try congruence.
specialize (H8 v fsig A P' Q' _ (necR_refl _)).
rewrite <- Hge in H0.
unfold filter_genv in H0.
invSome.
assert (v = Vptr b Int.zero) by (destruct (type_of_global psi b); inv H6; auto).
subst v.
unfold val2adr in H1.
rewrite Int.signed_zero in H1.
subst loc.
spec H8. exists id. split; auto. exists b; auto.
exists b.
split.
hnf.
unfold eval_lvalue.
rewrite <- Hge.
rewrite H3.
unfold filter_genv.
rewrite H0.
destruct fsig. simpl @fst; simpl @snd.
destruct (type_of_global psi b); inv H6; auto.
rewrite eqb_type_refl. auto.
intro loc.
hnf.
if_tac; auto.
subst.
hnf. auto.
hnf; auto.
Qed.

Definition free_list_juicy_mem:
  forall jm bl m, free_list (m_dry jm) bl = Some m -> juicy_mem.
Admitted.

Lemma can_alloc_variables:
  forall jm vl, exists ve', exists jm',
          list_norepet (map (@fst _ _) vl) ->
          Csem.alloc_variables empty_env (m_dry jm) vl ve' (m_dry jm') /\
          (resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\ level jm = S (level jm')).
Admitted.


Lemma build_call_temp_env:
  forall f vl, 
     list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)) ->
  exists te,  bind_parameter_temps (fn_params f) vl
                     (create_undef_temps (fn_temps f)) = Some te.
Admitted.

Lemma resource_decay_funassert:
  forall G rho b w w',
         resource_decay b w w' ->
         app_pred (funassert G rho) w ->
         app_pred (funassert G rho) w'.
Admitted.

Lemma semax_call_aux:
 forall (Delta : tycontext) (G : funspecs) (A : Type)
  (P Q Q' : A -> list val -> pred rmap) (x : A) (F : pred rmap)
  (F0 : assert) (ret : option ident) (fsig : funsig) (a : expr)
  (bl : list expr) (R : ret_assert) (psi : genv) (k : cont) (rho : environ)
  (ora : Z) (jm : juicy_mem) (b : block) (id : ident),
   tc_expr Delta a rho (m_phi jm) ->
   tc_exprlist Delta bl rho (m_phi jm) ->
    map typeof bl = typelist2list (fst fsig) ->
    typecheck_environ rho Delta = true ->
    (snd fsig=Tvoid <-> ret=None) ->
    closed_wrt_modvars (Scall ret a bl) F0 ->
    R EK_normal nil = (fun rho0 : environ => F * Q x (get_result ret (snd fsig) rho0)) ->
    filter_genv psi = ge_of rho ->
    eval_expr rho a = Vptr b Int.zero ->
    (funassert G rho) (m_phi jm) ->
    (rguard Hspec psi Delta G F0 R k) (level (m_phi jm)) ->
    (believe Hspec G psi G) (level (m_phi jm)) ->
    In (id, mk_funspec fsig A P Q') G ->
    Genv.find_symbol psi id = Some b ->
    (forall vl : list val, (!|>(Q' x vl <=> Q x vl)) (m_phi jm)) ->
    (|>(F0 rho * F * P x (eval_exprlist rho bl))) (m_phi jm) ->
   jsafeN Hspec psi (level (m_phi jm)) ora
     (State (ve_of rho) (te_of rho) (Kseq (Scall ret a bl) :: k)) jm.
Proof.
intros Delta G A P Q Q' x F F0 ret fsig a bl R psi k rho ora jm b id.
intros TC1 TC2 TC4 TC3 TC5 H HR H0 H3 H4 H1 Prog_OK H8 H7 H11 H14.
pose (H6:=True); pose (H9 := True); pose (H16:=True);
pose (H12:=True); pose (H10 := True); pose (H5:=True).
(*************************************************)
assert (Prog_OK' := Prog_OK).
specialize (Prog_OK' (Vptr b Int.zero) fsig A P Q' _ (necR_refl _)).
(*************************************************)
case_eq (level (m_phi jm)); [solve [simpl; auto] | intros n H2].
simpl.
destruct (levelS_age1 _ _ H2) as [phi' H13].
assert (LATER: laterR (level (m_phi jm)) n) by (constructor 1; rewrite H2; reflexivity).
spec Prog_OK'.
hnf. exists id; split; auto.
exists b; split; auto.
clear H16.
clear H10 H6 H5 H8.
specialize (H14 _ (age_laterR H13)).
do 4 (pose proof I).
destruct Prog_OK'.
admit.  (* external case *)
destruct H15 as [b' [f [[? [? [? ?]]] ?]]].
destruct H18 as [H17' H18].
inversion H15; clear H15; subst b'.
specialize (H19 x n LATER).
rewrite semax_fold_unfold in H19.
apply (pred_nec_hereditary _ _ n (laterR_necR LATER)) in Prog_OK.
pose (F0F := fun _: environ => F0 rho * F).
specialize (H19 _ _ (necR_refl _) (Prog_OK)  
                      (Kseq (Sreturn None) :: Kcall ret f (ve_of rho) (te_of rho) :: k)
                       F0F _ (necR_refl _)).
unfold F0F in *; clear F0F.
spec H19 ; [clear H19 |].
split.
repeat intro; f_equal.
intros ek vl rho'.
unfold frame_ret_assert.
rewrite <- (sepcon_comm (stackframe_of f rho')).
unfold function_body_ret_assert.
destruct ek; try solve [normalize].
apply prop_andp_subp; intro.
repeat rewrite andp_assoc.
apply subp_trans' with
 (F0 rho * F * (stackframe_of f rho' * bind_ret vl (fn_return f) (Q x)) && funassert G rho').
apply andp_subp'; auto.
apply sepcon_subp'; auto.
apply sepcon_subp'; auto.
unfold bind_ret.
destruct vl.
destruct (fn_return f); auto.
apply pred_eq_e1; apply (H11 _ _ LATER).
destruct vl; auto.
apply andp_subp'; auto.
apply pred_eq_e1; apply (H11 _ _ LATER).
clear Q' H11.
pose proof I.
pose proof I.

intros wx ? w' ? ?.
assert (n >= level w')%nat.
apply necR_level in H21.
apply le_trans with (level wx); auto.
clear wx H20 H21.
intros ora' jm' ?.
subst w'.
destruct H15 as [H15 H20].
assert (FL: exists m2, free_list (m_dry jm')  (Csem.blocks_of_env (ve_of rho')) = Some m2).
admit.  (* prove this from H22, stackframe_of *)
destruct FL as [m2 FL].
pose (jm2 := free_list_juicy_mem _ _ _ FL).
assert (FL2: free_list (m_dry jm') (Csem.blocks_of_env (ve_of rho')) = Some (m_dry jm2)) by admit.
assert (FL3: level jm' = level jm2) by admit.
pose (rval := match vl with v::_ => v | nil => Vundef end).
pose (rho2 := match ret with
                      | None => rho
                      | Some rid => mkEnviron (ge_of rho) (ve_of rho) (PTree.set rid rval (te_of rho))
                      end).

specialize (H1 EK_normal nil rho2).
rewrite HR in H1; clear R HR. simpl exit_cont in H1.
specialize (H1 (m_phi jm2)).
spec H1; [ admit | ]. (* easy *)
specialize (H1 _ (necR_refl _)).
spec H1; [clear H1 | ].
split.
split.
admit.  (* typechecking proof, looks hard/impossible we don't know anything about rho2*)
unfold rho2; simpl ge_of. destruct ret; auto.
rewrite <- sepcon_assoc.
admit.  (* very plausible *)
hnf in H1.
specialize (H1 ora' jm2).
specialize (H1 (eq_refl _)).
case_eq (@level rmap ag_rmap (m_phi jm')); intros; [solve [auto] |].
destruct (levelS_age1 jm' _ H21) as [jm'' ?].
destruct (age_twin' jm' jm2 jm'') as [jm2'' [? ?]]; auto.
pose proof (age_safe _ _ _ _ H26 _ _ _ H1).
exists  (State (ve_of rho2) (te_of rho2) k); exists jm2''.
replace n0 with (level jm2'') by admit.  (* easy *) 
split; auto.
split.
simpl.
unfold rho2.
rewrite (age_jm_dry H26) in FL2.
destruct vl.
assert (f.(fn_return)=Tvoid).
clear - H22; unfold bind_ret in H22; destruct (f.(fn_return)); normalize in H22; try contradiction; auto.
unfold fn_funsig in H18. rewrite H28 in H18. rewrite H18 in TC5. simpl in TC5.
destruct TC5 as [TC5 _]; specialize (TC5 (eq_refl _)). rewrite TC5 in *.
apply step_return with f None Vundef (te_of rho); simpl; auto.
simpl.
assert (typecheck_val v (fn_return f) = true).
 clear - H22; unfold bind_ret in H22; destruct vl; normalize in H22; try contradiction; auto.
 destruct H22. destruct H. apply H.
destruct ret.
simpl.
unfold rval.
apply step_return with (zap_fn_return f) None v (PTree.set i v (te_of rho)); simpl; auto.
elimtype False.
clear - H28 H18 TC5. subst fsig. unfold fn_funsig in TC5. simpl in TC5.
destruct TC5. rewrite H0 in H28 by auto.
clear - H28. destruct v; simpl in *; congruence. (* typechecking proof, works when typecheck as void disabled*)
admit.  (* not too difficult *)
(* END OF  "spec H19" *)

destruct (can_alloc_variables jm (fn_vars f)) as [ve' [jm' [? ?]]].
auto.
rewrite <- Genv.find_funct_find_funct_ptr in H16.
destruct (build_call_temp_env f (eval_exprlist rho bl)) as [te' ?]; auto.
exists (State ve' te' (Kseq f.(fn_body) :: Kseq (Sreturn None) 
                                     :: Kcall ret f (ve_of rho) (te_of rho) :: k)).
exists  jm'.
split.
split; auto.
eapply step_call_internal with (vargs:=eval_exprlist rho bl); eauto.
4: unfold type_of_function; reflexivity.
admit. (* typechecking proof *)
rewrite <- H3.
eapply (eval_expr_relate _ _ _ _ _ H0 TC3 TC1).
admit. (* typechecking proof, make a lemma for this one *)

pose (rho3 := mkEnviron (ge_of rho) ve' te').
assert (n >= level jm')%nat.
destruct H20. clear - H22 H2.
change (level (m_phi jm)) with (level jm) in H2.
omega.
assert (app_pred (funassert G rho3) (m_phi jm')).
clear - H4 H20. destruct H20 as [? _].
apply (resource_decay_funassert _ _ _ _ _ H) in H4.
unfold rho3; clear rho3.
apply H4.
specialize (H19 rho3 _ H22 _ (necR_refl _)).
spec H19; [clear H19|].
split; [split|]; auto.
hnf. unfold func_tycontext.
admit. (* typechecking proof *)
normalize.
split; auto.
unfold bind_args.
unfold rho3 at 1.
simpl te_of.
rewrite <- sepcon_assoc.
normalize.
split.
hnf.
clear - TC2 H21 TC4 H17.
admit.  (* should be easy *)
admit.  (* plausible  *)
(* end   "spec H19" *)

specialize (H19 ora jm').
apply age_level in H13.
destruct H20.
change (level jm = S n) in H2. rewrite H2 in H24; inv H24.
apply H19.
unfold rho3; simpl; auto.
Qed.

Lemma semax_call: 
forall Delta G A (P Q: A -> list val -> pred rmap) x F ret fsig a bl,
      match_fsig fsig bl ret = true ->
       semax Hspec Delta G
         (fun rho => 
           tc_expr Delta a rho && tc_exprlist Delta bl rho  && 
         (fun_assert  (eval_expr rho a) fsig A P Q && 
          (F * P x (eval_exprlist rho bl) )))
         (Scall ret a bl)
         (normal_ret_assert (fun rho => F * Q x (get_result ret (snd fsig) rho))).
Proof.
rewrite semax_unfold; intros.
destruct (match_fsig_e _ _ _ H) as [TC4 TC5]; clear H.
split.
apply prove_some_static_thing.
intros.
rename H0 into H1.
intro rho.
intros ? ? ? ? [[TC3 ?] ?].
assert (H0': necR w (level a')).
apply nec_nat. apply necR_level in H2. apply le_trans with (level y); auto.
eapply pred_nec_hereditary in H1; [ | apply H0'].
eapply pred_nec_hereditary in Prog_OK; [ | apply H0'].
clear w H0' H0 y H2.
rename a' into w.
destruct TC3 as [TC3 H0].
intros ora jm ?.
subst w.
apply extend_sepcon_andp in H3; auto.
destruct H3 as [H2 H3].
normalize in H3.
destruct H3 as [[b [H3 H6]] H5].
specialize (H6 (b,0)).
rewrite jam_true in H6 by auto.
hnf in H3.
generalize H4; intros [_ H7].
specialize (H7 (b,0) (mk_funspec fsig A P Q) _ (necR_refl _) H6).
destruct H7 as [id [v [[H7 H8] H9]]].
hnf in H9.
simpl in H8. unfold val2adr in H8. destruct v; try contradiction.
symmetry in H8; inv H8.
destruct H2 as [TC1 TC2].
assert (H8: exists fs, In (id,fs) G).
admit.  (* easy *)
destruct H8 as [fs H8].
generalize H4; intros [H10 _].
specialize (H10 id fs _ (necR_refl _) H8).
destruct H10 as [v' [b' [[H10 H11] H13]]].
simpl in H10. inversion2 H7 H10.
simpl in H11. subst b'.
unfold func_at in H13.
rewrite H12 in H13.
destruct fs as [fsig' A' P' Q'].
assert (fsig' = fsig) by (destruct fsig, fsig'; inv H15; auto).
clear H15; subst fsig'.
hnf in H6,H13.
rewrite H6  in H13.
change (In (id, mk_funspec fsig A' P' Q') G) in H8.
inversion H13; clear H13.
subst A'.
apply inj_pair2 in H11. rename H11 into H15.
clear H6; pose (H6:=True).
clear H9; pose (H9:=True).
rewrite <- H0 in H7.
unfold filter_genv in H7.
invSome.
assert (b0=b/\ i=Int.zero) by (destruct (type_of_global psi b0); inv H11; auto).
destruct H2; subst b0 i.
clear H11. pose (H16:=True).
clear H12; pose (H12:=True).
set (args := eval_exprlist rho bl).
fold args in H5.
destruct (function_pointer_aux A P P' Q Q' (m_phi jm)) as [H10 H11].
f_equal; auto.
clear H15.
specialize (H10 x args).
specialize (H11 x).
rewrite <- sepcon_assoc in H5.
assert (H14: app_pred (|> (F0 rho * F * P' x args)) (m_phi jm)).
do 3 red in H10.
apply eqp_later1 in H10.
rewrite later_sepcon.
apply pred_eq_e2 in H10.
eapply (sepcon_subp' (|>(F0 rho * F)) _ (|> P x args) _ (level (m_phi jm))); eauto.
rewrite <- later_sepcon. apply now_later; auto.
eapply semax_call_aux; try eassumption.
unfold normal_ret_assert.
extensionality rho'.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
auto.
Qed.

Lemma semax_call_ext:
     forall Delta G P Q ret a bl a' bl',
      typeof a = typeof a' ->
      (forall rho, typecheck_environ rho Delta = true ->
                        P rho |-- !! (eval_expr rho a = eval_expr rho a' /\
                                           eval_exprlist rho bl = eval_exprlist rho bl')) ->
  semax Hspec Delta G P (Scall ret a bl) Q ->
  semax Hspec  Delta G P (Scall ret a' bl') Q.
Proof.
intros.
rewrite semax_unfold in H1|-*.
destruct H1; split; auto.
apply prove_some_static_thing.
intros.
specialize (H2 psi w Prog_OK k F H3 H4).
intro rho; specialize (H2 rho).
intros ? ? ? ? ?.
specialize (H2 y H5 a'0 H6 H7).
destruct H7 as [[? ?] _].
destruct H7.
hnf in H2|-*; intros.
specialize (H2 ora jm H10).
eapply convergent_controls_safe; try apply H2.
reflexivity.
simpl; intros ? ?. unfold cl_after_external. destruct ret0; auto.
reflexivity.
intros.
destruct H8 as [w1 [w2 [_ [_ ?]]]].
specialize (H0 _ H7 _ H8).
destruct H0.
assert (forall vf, Clight_sem.eval_expr psi (ve_of rho) (te_of rho) (m_dry jm) a vf
               -> Clight_sem.eval_expr psi (ve_of rho) (te_of rho) (m_dry jm) a' vf).
clear - H H0 H1 H7 H9 .
admit.  (* typechecking proof, without typechecking on a we can't do relate
                               Also need uniqueness proof for eval_expr *) 
assert (forall tyargs vargs, 
             Clight_sem.eval_exprlist psi (ve_of rho) (te_of rho) (m_dry jm) bl tyargs vargs ->
             Clight_sem.eval_exprlist psi (ve_of rho) (te_of rho) (m_dry jm) bl' tyargs vargs).
clear - H12 H1 H7.
admit.  (* typechecking proof, same difficulties as above *) 
destruct H11; split; auto.
inv H11; [eapply step_call_internal | eapply step_call_external ]; eauto.
rewrite <- H; auto.
rewrite <- H; auto.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Admitted.

Lemma  semax_return :
   forall Delta G R ret,
      (*Some typechecking thing*)
      semax Hspec Delta G 
                (fun rho => R EK_return (eval_exprlist rho (opt2list ret)) rho)
                (Sreturn ret)
                R.
Proof.
intros.
split.
apply prove_some_static_thing.
intros.
rewrite semax_fold_unfold.
intro psi.
apply derives_imp.
clear n.
intros w ? k F.
intros w' ? ?.
clear H.
clear w H0.
rename w' into w.
destruct H1.
do 3 red in H.
intro rho.
intros n ? w' ? ?.
assert (necR w (level w')).
apply nec_nat.
apply necR_level in H2.
apply le_trans with (level n); auto.
apply (pred_nec_hereditary _ _ _ H4) in H0.
clear w n H2 H1 H4.
destruct H3 as [[[? H4] ?] ?].
specialize (H0 EK_return (eval_exprlist rho (opt2list ret)) rho).
specialize (H0 _ (le_refl _) _ (necR_refl _)).
spec H0.
split; auto.
split; auto.
split; auto.
intros ? ? ?.
specialize (H0 ora jm H5).
eapply convergent_controls_safe; try apply H0.
simpl; auto.
intros ? ?; simpl.
unfold cl_after_external.
auto.
simpl; auto.
intros.
simpl in H6.
destruct H6; split; auto.
revert H6; simpl.
destruct ret. simpl.
case_eq (call_cont k); intros.
inv H8.
inv H13.
destruct c.
elimtype False; clear - H6.
admit.  (* easy *)
elimtype False; clear - H6.
admit.  (* easy *)
elimtype False; clear - H6.
admit.  (* easy *)
elimtype False; clear - H6.
admit.  (* easy *)
destruct l0.
clear H0 H2 H7.
inv H8.
destruct optid.
destruct H16; congruence.
inv H10.
destruct H16.
econstructor; try eassumption; simpl.
2: split; [congruence | eassumption].
exists (eval_expr rho e).
split.

admit.  (* typechecking proof *)
admit.  (* typechecking proof, but this will be difficult because I think there's not enough
                 information to know that f is really the same as the function that Delta assumes *)
inv H8.
destruct optid.
destruct H19; congruence.
symmetry in H13; inv H13.
destruct H19.
elimtype False.
admit.  (* typechecking proof, but this will be difficult because I think there's not enough
                 information to know that f is really the same as the function that Delta assumes;
               if we could know that, then the fact that fn_return f = Tvoid would do it *)
simpl.
intro.
inv H6.
econstructor; try eassumption.
rewrite call_cont_idem in H12; auto.
Qed.

End extensions.
