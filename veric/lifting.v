(* A core wp-based separation logic for Clight, in the Iris style. Maybe VeriC can be built on top of this? *)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax.
Require Import VST.veric.semax_straight.
Require Import VST.veric.semax_call.

Global Instance local_absorbing `{!heapGS Σ} l : Absorbing (local l).
Proof.
  rewrite /local; apply monPred_absorbing, _.
Qed.

Global Instance local_persistent `{!heapGS Σ} l : Persistent (local l).
Proof.
  rewrite /local; apply monPred_persistent, _.
Qed.

Section mpred.

Context `{!VSTGS OK_ty Σ} (OK_spec : ext_spec OK_ty) (ge : genv).

Definition wp_expr e Φ : assert :=
  ∀ m, ⎡juicy_mem.mem_auth m⎤ -∗
         ∃ v, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_expr ge ve te m e v (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡juicy_mem.mem_auth m⎤ ∗ Φ v.

Definition wp_lvalue e Φ : assert :=
  ∀ m, ⎡juicy_mem.mem_auth m⎤ -∗
         ∃ b o, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_lvalue ge ve te m e b o Full (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡juicy_mem.mem_auth m⎤ ∗ Φ (Vptr b o).


Lemma wp_expr_mono : forall e P1 P2, (∀ v, P1 v ⊢ P2 v) → wp_expr e P1 ⊢ wp_expr e P2.
Proof.
  intros; rewrite /wp_expr.
  by repeat f_equiv.
Qed.

Definition assert_safe
     (E: coPset) (f: function) (ctl: contx) rho : iProp Σ :=
       ∀ ora ve te,
       ⌜rho = construct_rho (filter_genv ge) ve te⌝ →
       match ctl with
       | Stuck => |={E}=> False
       | Cont (Kseq s ctl') => 
             jsafeN OK_spec ge E ora (State f s ctl' ve te)
       | Cont (Kloop1 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f Sskip (Kloop1 body incr ctl') ve te)
       | Cont (Kloop2 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f (Sloop body incr) ctl' ve te)
       | Cont (Kcall id' f' ve' te' k') => 
             jsafeN OK_spec ge E ora (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)
       | Cont Kstop => (* should this be Returnstate instead? *)
             jsafeN OK_spec ge E ora (State f (Sreturn None) Kstop ve te)
       | Cont _ => |={E}=> False
       | Ret None ctl' =>
                jsafeN OK_spec ge E ora (State f (Sreturn None) ctl' ve te)
       | Ret (Some v) ctl' => ∀ e, (∀ m, juicy_mem.mem_auth m -∗ ⌜∃ v', Clight.eval_expr ge ve te m e v' ∧ Cop.sem_cast v' (typeof e) (fn_return f) m = Some v⌝) →
           jsafeN OK_spec ge E ora (State f (Sreturn (Some e)) ctl' ve te)
       end.

Lemma assert_safe_mono E1 E2 f ctl rho: E1 ⊆ E2 ->
  assert_safe E1 f ctl rho ⊢ assert_safe E2 f ctl rho.
Proof.
  rewrite /assert_safe; intros.
  iIntros "H" (??? ->); iSpecialize ("H" $! _ _ _ eq_refl).
  destruct ctl.
  - iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
  - destruct c; try by iApply jsafe_mask_mono.
    iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
  - destruct o; last by iApply jsafe_mask_mono.
    iStopProof; do 3 f_equiv.
    by iApply jsafe_mask_mono.
Qed.

Definition guarded E f k Q := ∀ rho,
  (RA_normal Q rho -∗ assert_safe E f (Cont k) rho) ∧
  (RA_break Q rho -∗ assert_safe E f (break_cont k) rho) ∧
  (RA_continue Q rho -∗ assert_safe E f (continue_cont k) rho) ∧
  (RA_return Q None rho -∗ assert_safe E f (Ret None (call_cont k)) rho) ∧
  (∀ e, wp_expr e (λ v, RA_return Q (Some v)) rho -∗
    ∀ ora ve te, ⌜rho = construct_rho (filter_genv ge) ve te⌝ →
    jsafeN OK_spec ge E ora (State f (Sreturn (Some e)) (call_cont k) ve te)).

Lemma guarded_normal : forall E f k P,
  guarded E f k (normal_ret_assert P) ⊣⊢ (∀ rho, P rho -∗ assert_safe E f (Cont k) rho).
Proof.
  intros.
  iSplit.
  { iIntros "H" (rho); iDestruct ("H" $! rho) as "[$ _]". }
  iIntros "H" (?); iSplit; first done.
  simpl; monPred.unseal.
  repeat (iSplit; first by iIntros "[]").
  iIntros (?) "He".
  rewrite /wp_expr; monPred.unseal.
  iIntros (????).
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  iDestruct ("He" with "[%] Hm") as (??) "(? & [])"; done.
Qed.

Lemma stackframe_of_freeable_blocks:
  forall f rho ve,
      Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f) ->
      list_norepet (map fst (fn_vars f)) ->
      ve_of rho = make_venv ve ->
      typecheck_var_environ (λ id : positive, ve !! id) (make_tycontext_v (fn_vars f)) ->
      match_venv (ve_of rho) (fn_vars f) ->
       stackframe_of' (genv_cenv ge) f rho ⊢ freeable_blocks (blocks_of_env ge ve).
Proof.
 intros until ve.
 intros COMPLETE.
 intros ??? H7.
 unfold stackframe_of'.
 unfold blocks_of_env.
 trans (foldr bi_sep emp (map (fun idt => var_block' Share.top (genv_cenv ge) idt rho) (fn_vars f))).
 { clear; induction (fn_vars f); simpl; auto; monPred.unseal. rewrite -IHl; by monPred.unseal. }
 unfold var_block'. unfold eval_lvar. monPred.unseal; simpl.
 rewrite H0. unfold make_venv. forget (ge_of rho) as ZZ. rewrite H0 in H7; clear rho H0.
 revert ve H1 H7; induction (fn_vars f); simpl; intros.
 case_eq (Maps.PTree.elements ve); simpl; intros; auto.
 destruct p as [id ?].
 pose proof (Maps.PTree.elements_complete ve id p). rewrite H0 in H2. simpl in H2.
 specialize (H7 id). unfold make_venv in H7. rewrite H2 in H7; auto.
 destruct p; inv H7.
 inv H.
 destruct a as [id ty]. simpl in *.
 simpl in COMPLETE. inversion COMPLETE; subst.
 clear COMPLETE; rename H5 into COMPLETE; rename H2 into COMPLETE_HD.
 specialize (IHl COMPLETE H4 (Maps.PTree.remove id ve)).
 assert (exists b, Maps.PTree.get id ve = Some (b,ty)). {
  specialize (H1 id ty).
  rewrite Maps.PTree.gss in H1. destruct H1 as [[b ?] _]; auto. exists b; apply H.
 }
 destruct H as [b H].
 destruct (@Maps.PTree.elements_remove _ id (b,ty) ve H) as [l1 [l2 [? ?]]].
 rewrite H0.
 rewrite map_app. simpl map.
 trans (freeable_blocks ((b,0,@Ctypes.sizeof ge ty) :: (map (block_of_binding ge) (l1 ++ l2)))).
 2:{
   clear.
   induction l1; simpl; try auto.
   destruct a as [id' [hi lo]]. simpl in *.
   rewrite -IHl1.
   rewrite !assoc (comm _ (VALspec_range _ _ _ )) //. }
 unfold freeable_blocks; simpl. rewrite <- H2.
 apply bi.sep_mono.
 { unfold Map.get. rewrite H. rewrite Cop2.eqb_type_refl.
   unfold memory_block. iIntros "(% & % & H)".
   rename H6 into H99.
   rewrite memory_block'_eq.
   2: rewrite Ptrofs.unsigned_zero; lia.
   2:{ rewrite Ptrofs.unsigned_zero. rewrite Zplus_0_r.
       rewrite Z2Nat.id.
       change (Ptrofs.unsigned Ptrofs.zero) with 0 in H99.
       lia.
       pose proof (@sizeof_pos (genv_cenv ge) ty); lia. }
 rewrite Z.sub_0_r.
 unfold memory_block'_alt.
 rewrite -> if_true by apply readable_share_top.
 rewrite Z2Nat.id //.
 + pose proof (@sizeof_pos (genv_cenv ge) ty); lia. }
 etrans; last apply IHl.
 clear - H3.
 induction l; simpl; auto.
 destruct a as [id' ty']. simpl in *.
 apply bi.sep_mono; auto.
 replace (Map.get (fun id0 : positive => Maps.PTree.get id0 (Maps.PTree.remove id ve)) id')
   with (Map.get (fun id0 : positive => Maps.PTree.get id0 ve) id'); auto.
 unfold Map.get.
 rewrite Maps.PTree.gro; auto.
 intros id' ty'; specialize (H1 id' ty').
 { split; intro.
 - destruct H1 as [H1 _].
   assert (id<>id').
   intro; subst id'.
   clear - H3 H5; induction l; simpl in *. rewrite Maps.PTree.gempty in H5; inv H5.
   destruct a; simpl in *.
   rewrite Maps.PTree.gso in H5. auto. auto.
   destruct H1 as [v ?].
   rewrite Maps.PTree.gso; auto.
   exists v. unfold Map.get. rewrite Maps.PTree.gro; auto.
 - unfold Map.get in H1,H5.
   assert (id<>id').
     clear - H5; destruct H5. intro; subst. rewrite Maps.PTree.grs in H. inv H.
   rewrite -> Maps.PTree.gro in H5 by auto.
   rewrite <- H1 in H5. rewrite -> Maps.PTree.gso in H5; auto. }
 hnf; intros.
 destruct (make_venv (Maps.PTree.remove id ve) id0) eqn:H5; auto.
 destruct p.
 unfold make_venv in H5.
 destruct (peq id id0).
 subst. rewrite Maps.PTree.grs in H5. inv H5.
 rewrite -> Maps.PTree.gro in H5 by auto.
 specialize (H7 id0). unfold make_venv in H7. rewrite H5 in H7.
 destruct H7; auto. inv H6; congruence.
Qed.

Lemma free_stackframe :
  forall f m ve te
  (NOREP: list_norepet (map (@fst _ _) (fn_vars f)))
  (COMPLETE: Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f)),
      typecheck_var_environ (λ id : positive, ve !! id) (make_tycontext_v (fn_vars f)) ->
      match_venv (make_venv ve) (fn_vars f) ->
   juicy_mem.mem_auth m ∗ stackframe_of' (genv_cenv ge) f (construct_rho (filter_genv ge) ve te) ⊢
   |==> ∃ m2, ⌜free_list m (blocks_of_env ge ve) = Some m2⌝ ∧ juicy_mem.mem_auth m2.
Proof.
  intros.
  iIntros "(Hm & stack)".
  rewrite stackframe_of_freeable_blocks //.
  clear.
  forget (blocks_of_env ge ve) as el.
  iInduction el as [|] "IHel" forall (m); first eauto.
  destruct a as ((id, b), t); simpl.
  iDestruct "stack" as "(H & stack)".
  iDestruct (juicy_mem_lemmas.VALspec_range_can_free with "[$Hm $H]") as %(m' & ?).
  rewrite /= Zplus_minus in H; rewrite H.
  iMod (juicy_mem_lemmas.VALspec_range_free with "[$Hm $H]") as "Hm"; first done.
  iApply ("IHel" with "Hm stack").
Qed.

Lemma safe_return : forall E f ora ve te (Hexit : forall m i, ext_spec_exit OK_spec (Some i) ora m),
  f.(fn_vars) = [] → True ⊢ jsafeN OK_spec ge E ora (State f (Sreturn None) Kstop ve te).
Proof.
  intros.
  iIntros "?".
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & ?)".
  iMod (free_stackframe f  _ ve te with "[$Hm]") as (??) "?"; rewrite ?H; try eassumption; try solve [constructor].
  { admit. }
  { admit. }
  { rewrite /stackframe_of' H /=.
    by monPred.unseal. }
  iIntros "!>"; iExists _, _; iSplit.
Check step_return_1.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  rewrite jsafe_unfold /jsafe_pre.
  iIntros "!> !>" (?) "?"; iLeft.
  simpl.
  iExists Int.zero; iPureIntro; auto.
Admitted.

Lemma guarded_stop : forall E f P (Hexit : forall ora m i, ext_spec_exit OK_spec (Some i) ora m),
  f.(fn_vars) = [] →
  True ⊢ guarded E f Kstop (function_body_ret_assert Tvoid P).
Proof.
  intros; iIntros "?" (?).
  simpl; monPred.unseal.
  iSplit.
  - iIntros "H"; rewrite /assert_safe /=.
    iIntros (??? ->).
    by iApply safe_return.
  - do 2 (iSplit; first by iIntros "[]").
    iSplit.
    + iIntros "H"; rewrite /assert_safe /=.
      iIntros (??? ->).
      by iApply safe_return.
    + iIntros "% H" (??? ->).
      iApply jsafe_step.
      rewrite /wp_expr /jstep_ex; monPred.unseal.
      iIntros (?) "(Hm & ?)".
      iDestruct ("H" with "[%] Hm") as (??) "(? & [] & ?)"; done.
Qed.

Definition wp E f s (Q : ret_assert) : assert := assert_of (λ rho,
    ∀ k, (* ▷ *) guarded E f k Q -∗ assert_safe E f (Cont (Kseq s k)) rho).
(* ▷ would make sense here, but removing Kseq isn't always a step: for instance, Sskip Kstop is a synonym
   for (Sreturn None) Kstop rather than stepping to it. *)

Lemma wp_seq : forall E f s1 s2 Q, wp E f s1 (normal_ret_assert (wp E f s2 Q)) ⊢ wp E f (Ssequence s1 s2) Q.
Proof.
  intros; rewrite /wp; split => rho.
  iIntros "H % Hk" (??? ->).
  iApply jsafe_local_step.
  { intros; constructor. }
  iApply ("H" with "[Hk]"); last done.
  rewrite guarded_normal; simpl.
  by iIntros (?) "H"; iApply "H".
Qed.

Definition valid_val v :=
  match v with Vptr _ _ => expr.valid_pointer v | _ => True end.

Definition valid_val0 m v : Prop :=
  match v with Vptr b o => valid_pointer m b (Ptrofs.intval o) = true | _ => True end.

Lemma valid_val_mem : forall m v, juicy_mem.mem_auth m ∗ valid_val v ⊢ ⌜valid_val0 m v⌝.
Proof.
  iIntros (??) "(Hm & Hv)"; destruct v; try done.
  iApply expr_lemmas4.valid_pointer_dry0; iFrame.
Qed.

Lemma bool_val_valid : forall m v t b, valid_val0 m v -> Cop2.bool_val t v = Some b -> bool_val v t m = Some b.
Proof.
  rewrite /Cop2.bool_val /bool_val.
  intros; destruct t; try done; simpl.
  - destruct i; done.
  - destruct v; try done.
    simpl in *.
    simple_if_tac; try done.
    rewrite /weak_valid_pointer H //.
  - destruct f; done.
  - destruct (Cop2.eqb_type _ _); try done.
    rewrite /Cop2.bool_val_p in H0.
    simple_if_tac.
    + destruct v; try done.
      rewrite /weak_valid_pointer H //.
    + destruct v; try done.
      rewrite /weak_valid_pointer H //.
Qed.

Lemma wp_if: forall E f e s1 s2 R,
  wp_expr e (λ v, ⎡valid_val v⎤ ∧ ∃ b, ⌜Cop2.bool_val (typeof e) v = Some b⌝ ∧ if b then wp E f s1 R else wp E f s2 R)
  ⊢ wp E f (Sifthenelse e s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H % Hk" (??? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (??) "(Hm & H)"; first done.
  iDestruct (valid_val_mem with "[Hm H]") as %?.
  { rewrite bi.and_elim_l; iFrame. }
  rewrite bi.and_elim_r; iDestruct "H" as (b ?) "H".
  iIntros "!>"; iExists _, m.
  iSplit.
  { iPureIntro.
    econstructor; eauto.
    apply bool_val_valid; eauto. }
  iFrame.
  destruct b; simpl; iNext; iApply ("H" with "[-]"); done.
Qed.

(* see also semax_lemmas.derives_skip *)
Lemma safe_skip : forall E ora f k ve te,
  assert_safe E f (exit_cont EK_normal None k) (construct_rho (filter_genv ge) ve te) ⊢
  jsafeN OK_spec ge E ora (State f Sskip k ve te).
Proof.
  intros; iIntros "H".
  rewrite /assert_safe.
  iSpecialize ("H" with "[%]"); first done.
  destruct k as [ | s ctl' | | | |]; try done; try solve [iApply (jsafe_local_step with "H"); constructor].
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
  - iMod "H" as "[]".
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
Qed.

Lemma wp_skip: forall E f R, RA_normal R ⊢ wp E f Sskip R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (??? ->).
  iDestruct ("Hk" $! _) as "[Hk _]".
  by iApply safe_skip; iApply "Hk".
Qed.

Lemma wp_set: forall E f i e R,
  wp_expr e (λ v, assert_of (subst i (liftx v) (RA_normal R))) ⊢ wp E f (Sset i e) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (??? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (??) "(Hm & H)"; first done.
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; constructor; eauto. }
  iFrame.
  iNext; simpl.
  iDestruct ("Hk" $! _) as "[Hk _]".
  iApply safe_skip; iApply "Hk".
  rewrite /subst /env_set /construct_rho /= expr_lemmas.map_ptree_rel //.
Qed.

Lemma wp_store: forall E f e1 e2 R,
  wp_expr (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ wp_lvalue e1 (λ v1,
    ∃ sh, ⌜writable0_share sh⌝ ∧ ⎡mapsto_ sh (typeof e1) v1⎤ ∗
    (⎡mapsto sh (typeof e1) v1 v2⎤ ={E}=∗ RA_normal R)))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (??? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (? He2) "(Hm & % & H)"; first done.
  iDestruct ("H" with "[%] Hm") as (b o ?) "(Hm & H)"; first done.
  iDestruct "H" as (sh ?) "(Hp & H)".
  iDestruct (mapsto_pure_facts with "Hp") as %((? & ?) & ?).
  iDestruct (mapsto_can_store with "[$Hm Hp]") as %(? & ?); [done.. |].
  iMod (mapsto_store with "[$Hm $Hp]") as "(Hm & Hp)"; [done.. |].
  iMod ("H" with "[%] Hp"); first done.
  iIntros "!>".
  specialize (He2 _ _ _ eq_refl); inv He2.
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iFrame.
  iNext.
  by iApply safe_skip; iApply "Hk".
  { inv H5. }
Qed.

Lemma wp_loop: forall E f s1 s2 R,
  ▷ wp E f s1 (normal_ret_assert (▷ wp E f s2 (normal_ret_assert (wp E f (Sloop s1 s2) R)))) ⊢ wp E f (Sloop s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  monPred.unseal.
  iIntros "H % Hk" (??? ->).
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[Hk]"); last done.
  rewrite guarded_normal.
  iIntros (?) "H"; simpl.
  iIntros (??? ->).
  iApply jsafe_local_step.
  { intros; constructor; auto. }
  iNext.
  iApply ("H" with "[Hk]"); last done.
  rewrite guarded_normal.
  iIntros (?) "H"; simpl.
  by iApply ("H" with "Hk").
Qed.

Lemma wp_continue: forall E f R,
  RA_continue R ⊢ wp E f Scontinue R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H % Hk".
  iDestruct ("Hk" $! _) as "(_ & _ & Hk & _)".
  iSpecialize ("Hk" with "H").
  simpl exit_cont; iIntros (??? ->); iSpecialize ("Hk" with "[%]"); first done.
  destruct (continue_cont k) eqn:Hcont.
  - iMod "Hk" as "[]".
  - rename c into k'.
    assert (exists s c, k' = Kseq s c) as (? & ? & Hcase).
    { induction k; inv Hcont; eauto. }
    rewrite Hcase.
    iInduction k as [| | | | |] "IHk" forall (k' Hcont Hcase); try discriminate.
    + iApply jsafe_local_step.
      { constructor. }
      iApply ("IHk" with "[%] [%] Hk"); eauto.
    + inv Hcont.
      iApply jsafe_local_step.
      { intros; apply step_skip_or_continue_loop1; auto. }
      iApply "Hk".
    + iApply jsafe_local_step.
      { apply step_continue_switch. }
      iApply ("IHk" with "[%] [%] Hk"); eauto.
  - exfalso; clear - Hcont.
    revert c o Hcont; induction k; simpl; intros; try discriminate; eauto.
Qed.

Lemma wp_break: forall E f R,
  RA_break R ⊢ wp E f Sbreak R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H % Hk".
  iDestruct ("Hk" $! _) as "(_ & Hk & _)".
  iSpecialize ("Hk" with "H").
  simpl exit_cont; iIntros (??? ->); iSpecialize ("Hk" with "[%]"); first done.
  destruct (break_cont k) eqn: Hcont.
  { iMod "Hk" as "[]". }
  2: { exfalso; clear - Hcont. revert k c Hcont; induction k; simpl; intros; try discriminate. eauto. }
  destruct c; try iMod "Hk" as "[]".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
  - rename c into k'.
    iInduction k as [| s' | s1 s2 | s1 s2 | |] "IHk" forall (s k' Hcont); try discriminate.
    + iApply jsafe_local_step.
      { constructor. }
      by iApply ("IHk" with "[%] Hk").
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { intros; apply step_skip_break_switch; auto. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
Qed.

(* It would be nice to decompose this into repeated wp_expr, but it includes typecasts. *)
Definition wp_exprs es ts Φ : assert :=
  ∀ m, ⎡juicy_mem.mem_auth m⎤ -∗
         ∃ vs, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_exprlist ge ve te m es ts vs (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡juicy_mem.mem_auth m⎤ ∗ Φ vs.

Lemma alloc_stackframe:
  forall m f te
      (COMPLETE: Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f))
      (Hsize: Forall (fun var => @Ctypes.sizeof ge (snd var) <= Ptrofs.max_unsigned) (fn_vars f)),
      list_norepet (map fst (fn_vars f)) ->
      juicy_mem.mem_auth m ⊢ |==> ∃ m' ve, ⌜Clight.alloc_variables ge empty_env m (fn_vars f) ve m' ∧ match_venv (make_venv ve) (fn_vars f)⌝ ∧
        juicy_mem.mem_auth m' ∗ stackframe_of' (genv_cenv ge) f (construct_rho (filter_genv ge) ve te).
Proof.
  intros.
  cut (juicy_mem.mem_auth m ⊢ |==> ∃ (m' : Memory.mem) (ve : env),
    ⌜(∀i, sub_option (empty_env !! i)%maps (ve !! i)%maps) ∧ alloc_variables ge empty_env m (fn_vars f) ve m'⌝
    ∧ juicy_mem.mem_auth m' ∗ stackframe_of' (genv_cenv ge) f (construct_rho (filter_genv ge) ve te)).
  { intros Hgen; rewrite Hgen; iIntros ">(% & % & (% & %) & ?) !>".
    iExists _, _; iFrame; iPureIntro; repeat (split; auto).
    eapply alloc_vars_match_venv; eauto. }
  rewrite /stackframe_of'.
  forget (fn_vars f) as vars. clear f.
  assert (forall i, In i (map fst vars) -> empty_env !! i = None) as Hout.
  { intros; apply Maps.PTree.gempty. }
  forget empty_env as ve0.
  revert ve0 m Hout Hsize; induction vars; intros; simpl; iIntros "Hm".
  - iExists m, ve0; iFrame; monPred.unseal; iPureIntro.
    split; auto; split; auto.
    + intros; apply sub_option_refl.
    + constructor.
  - destruct a as (id, ty).
    destruct (Mem.alloc m 0 (@sizeof (genv_cenv ge) ty)) as (m', b) eqn: Halloc.
    inv COMPLETE; inv Hsize; inv H.
    iMod (alloc_block with "Hm") as "(Hm & block)"; first done.
    { pose proof @sizeof_pos (genv_cenv ge) ty; unfold sizeof, Ptrofs.max_unsigned in *; simpl in *; lia. }
    unshelve iMod (IHvars _ _ (Maps.PTree.set id (b,ty) ve0) with "Hm") as (?? (Hsub & ?)) "(Hm & ?)"; try done.
    { intros; rewrite Maps.PTree.gso //; last by intros ->.
      apply Hout; simpl; auto. }
    iIntros "!>"; iExists _, _; monPred.unseal; iFrame.
    rewrite /var_block' /eval_lvar; monPred.unseal; simpl.
    replace (Map.get _ _) with (Some (b, ty)).
    rewrite Cop2.eqb_type_refl; iFrame; iPureIntro; simpl.
    + split; last done; split.
      * intros i; specialize (Hsub i).
        destruct (eq_dec i id); last by rewrite Maps.PTree.gso in Hsub.
        subst; rewrite Hout //; simpl; auto.
      * econstructor; eauto.
    + rewrite /Map.get /=.
      specialize (Hsub id); rewrite Maps.PTree.gss // in Hsub.
Qed.

Lemma wp_call: forall E f0 e es R,
  wp_expr e (λ v, ∃ f, ⌜exists b, v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr ge b = Some (Internal f) /\
    classify_fun (typeof e) =
    fun_case_f (type_of_params (fn_params f)) (fn_return f) (fn_callconv f) /\
    Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst f.(fn_params) ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok (genv_cenv ge) (f.(fn_vars))⌝ ∧
    wp_exprs es (type_of_params (fn_params f)) (λ vs, ▷ assert_of (λ rho,
      ∀ rho', stackframe_of' (genv_cenv ge) f rho' -∗ ▷ wp E f f.(fn_body) (normal_ret_assert (assert_of (λ rho'', stackframe_of' (genv_cenv ge) f rho'' ∗ RA_normal R rho))) rho'))) ⊢
  wp E f0 (Scall None e es) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (??? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr /wp_exprs.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (? He) "(Hm & %f & %Hb & H)"; first done.
  destruct Hb as (b & -> & Hb & ? & ? & ? & ? & ?).
  iDestruct ("H" with "[%] Hm") as (vs Hes) "(Hm & H)"; first done.
  iIntros "!>".
  specialize (He _ _ _ eq_refl).
  specialize (Hes _ _ _ eq_refl).
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_step.
  rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  destruct (build_call_temp_env f vs) as (le & ?).
  { admit. }
  iMod (alloc_stackframe with "Hm") as (m' ve' (? & ?)) "(Hm & Hstack)"; [done..|].
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto.
    admit.
    admit. }
  iFrame.
  iApply ("H" with "[$] [Hk]"); last done.
  rewrite guarded_normal.
  iIntros "!>" (?) "(? & HR)".
  iIntros (??? ->).
  iApply jsafe_step.
  rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  iMod (free_stackframe with "[$]") as (m'' ?) "Hm"; [try done..|].
  { admit. }
  { admit. }
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  simpl.
  iApply safe_skip; iApply "Hk"; done.
Admitted.

Lemma wp_return_Some: forall E f e R,
  wp_expr e (λ v, RA_return R (Some v)) ⊢ wp E f (Sreturn (Some e)) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H % Hk" (??? ->).
  iApply (convergent_controls_jsafe _ _ _ (State f (Sreturn (Some e)) (call_cont k) ve te)); try done.
  { inversion 1; subst; try match goal with H : _ \/ _ |- _ => destruct H; done end.
    rewrite call_cont_idem; econstructor; eauto. }
  iDestruct ("Hk" $! _) as "(_ & _ & _ & _ & Hk)".
  iSpecialize ("Hk" with "H").
  by iApply "Hk".
Qed.

Lemma wp_return_None: forall E f R,
  RA_return R None ⊢ wp E f (Sreturn None) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H % Hk" (??? ->).
  iApply (convergent_controls_jsafe _ _ _ (State f (Sreturn None) (call_cont k) ve te)); try done.
  { inversion 1; subst; try match goal with H : _ \/ _ |- _ => destruct H; done end.
    rewrite call_cont_idem; econstructor; eauto. }
  iDestruct ("Hk" $! _) as "(_ & _ & _ & Hk & _)".
  by iApply ("Hk" with "H").
Qed.

End mpred.

(* adequacy: copied from veric/SequentialClight *)
Require Import VST.veric.external_state.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.semantics.

Class VSTGpreS (Z : Type) Σ := {
  VSTGpreS_inv :: invGpreS Σ;
  VSTGpreS_heap :: gen_heapGpreS share address resource Σ;
  VSTGpreS_funspec :: inG Σ (gmap_view.gmap_viewR address (@funspecO' Σ));
  VSTGpreS_ext :: inG Σ (excl_authR (leibnizO Z))
}.

Definition VSTΣ Z : gFunctors :=
  #[invΣ; gen_heapΣ share address resource; GFunctor (gmap_view.gmap_viewRF address funspecOF');
    GFunctor (excl_authR (leibnizO Z)) ].
Global Instance subG_VSTGpreS {Z Σ} : subG (VSTΣ Z) Σ → VSTGpreS Z Σ.
Proof. solve_inG. Qed.

Lemma init_VST: forall Z `{!VSTGpreS Z Σ} (z : Z),
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS Z Σ,
    let H : VSTGS Z Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ in
    (state_interp Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z) ∗ ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (ext_alloc z) as (?) "(? & ?)".
  iIntros "!>" (?); iExists (GenHeapGS _ _ _ _ γh γm), (FunspecG _ _ γf), _.
  rewrite /state_interp /juicy_mem.mem_auth /funspec_auth /=; iFrame.
  iSplit; [|done]. iPureIntro. apply juicy_mem.empty_coherent.
Qed.

Global Instance stepN_absorbing {PROP : bi} `{!BiFUpd PROP} n E1 E2 (P : PROP) `{!Absorbing P}: Absorbing (|={E1}[E2]▷=>^n P).
Proof.
  induction n; apply _.
Qed.

Lemma adequacy: forall `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} ge z q m n,
  state_interp m z ∗ jsafeN OK_spec ge ⊤ z q ⊢
  |={⊤}[∅]▷=>^n ⌜dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge n z q m⌝.
Proof.
  intros.
  iIntros "(S & Hsafe)".
  iLöb as "IH" forall (m z q n).
  destruct n as [|n]; simpl.
  { iPureIntro. constructor. }
  rewrite [in (environments.Esnoc _ "Hsafe" _)]/jsafeN jsafe_unfold /jsafe_pre.
  iMod ("Hsafe" with "S") as "[Hsafe_halt | [Hsafe_core | Hsafe_ext]]".
  - iDestruct "Hsafe_halt" as %(ret & Hhalt & Hexit).
    iApply step_fupd_intro; first done; iApply step_fupdN_intro; first done.
    iPureIntro; eapply safeN_halted; eauto.
  - iDestruct "Hsafe_core" as ">(%c' & %m' & % & s_interp & ▷jsafe)".
    iApply fupd_mask_intro; first done.
    iIntros "Hclose !>"; iMod "Hclose" as "_".
    iSpecialize ("IH" with "[$] [$]").
    iModIntro; iApply (step_fupdN_mono with "IH").
    iPureIntro. eapply safeN_step; eauto.
  - iDestruct "Hsafe_ext" as (ef args w (at_external & Hpre)) "Hpost".
    iAssert (|={⊤}[∅]▷=>^(S n) ⌜(∀ (ret : option val) m' z' n',
      Val.has_type_list args (sig_args (ef_sig ef))
      → Builtins0.val_opt_has_rettype ret (sig_res (ef_sig ef))
        → n' ≤ n
            → ext_spec_post OK_spec ef w
                (genv_symb_injective ge) (sig_res (ef_sig ef)) ret z' m'
              → ∃ q',
                  (after_external (cl_core_sem ge) ret q m' = Some q'
                   ∧ dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge n' z' q' m'))⌝) with "[-]" as "Hdry".
      2: { iApply (step_fupdN_mono with "Hdry"); iPureIntro; intros; eapply safeN_external; eauto. }
      iApply step_fupdN_mono; first by do 8 setoid_rewrite bi.pure_forall.
      repeat (setoid_rewrite step_fupdN_plain_forall; last done; [|apply _..]).
      iIntros (ret m' z' n' ????).
      iApply fupd_mask_intro; first done.
      iIntros "Hclose !>"; iMod "Hclose" as "_".
      iMod ("Hpost" with "[%] [%]") as (??) "(S & Hsafe)"; [done..|].
      iSpecialize ("IH" with "[$] [$]").
      iModIntro; iApply step_fupdN_le; [done..|].
      iApply (step_fupdN_mono with "IH"); eauto.
Qed.

Definition ext_spec_entails {M E Z} (es1 es2 : external_specification M E Z) :=
  (forall e x1 p tys args z m, ext_spec_pre es1 e x1 p tys args z m ->
     exists x2, ext_spec_pre es2 e x2 p tys args z m /\
       forall ty ret z' m', ext_spec_post es2 e x2 p ty ret z' m' ->
                            ext_spec_post es1 e x1 p ty ret z' m') /\
  (forall v z m, ext_spec_exit es1 v z m -> ext_spec_exit es2 v z m).

Lemma ext_spec_entails_refl : forall {M E Z} (es : external_specification M E Z), ext_spec_entails es es.
Proof.
  intros; split; eauto.
Qed.

Theorem ext_spec_entails_safe : forall {G C M Z} {genv_symb} Hcore es1 es2 ge n z c m
  (Hes : ext_spec_entails es1 es2),
  @step_lemmas.dry_safeN G C M Z genv_symb Hcore es1 ge n z c m -> @step_lemmas.dry_safeN G C M Z genv_symb Hcore es2 ge n z c m.
Proof.
  induction n as [n IHn] using lt_wf_ind; intros.
  inv H.
  - constructor.
  - eapply step_lemmas.safeN_step; eauto.
    eapply IHn; eauto.
  - destruct Hes as (Hes & ?).
    apply Hes in H1 as (x2 & ? & ?).
    eapply step_lemmas.safeN_external; eauto; intros.
    edestruct H2 as (c' & ? & ?); eauto.
    exists c'; split; auto.
    eapply IHn; eauto; [lia | by split].
  - destruct Hes.
    eapply step_lemmas.safeN_halted; eauto.
Qed.

Lemma wp_adequacy: forall `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty}
  (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
  (EXIT: forall `{!VSTGS OK_ty Σ} ora m i, ext_spec_exit Espec (Some i) ora m)
  ge m z f s ve te (Hf : f.(fn_vars) = []),
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ in
    local (λ rho, rho = construct_rho (filter_genv ge) ve te) ∧ ⎡state_interp m z⎤ ∗ ∃ R, wp Espec ge ⊤ f s (function_body_ret_assert Tvoid R)) →
       (forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem ge) dryspec
            ge n z (State f s Kstop ve te) m (*∧ φ*)) (* note that this includes ext_spec_exit if the program halts *).
Proof.
  intros.
(*  assert (forall n, @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem ge) dryspec
            ge n z (State f s Kstop ve te) m ∧ φ) as H'; last (split; [eapply H' | apply (H' 0)]; eauto). *)
  (*intros n;*)
  eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc'(Σ := Σ) _ (S n) O); [apply _..|].
  simpl; intros. apply (embed_emp_valid_inj(PROP2 := monPred environ_index _)). iIntros "_".
  iMod (H Hinv) as (???) "?".
  iStopProof.
  rewrite /wp; split => rho; monPred.unseal.
  iIntros "(% & S & H)".
  iApply step_fupd_intro; first done.
  iNext.
  set (HH := Build_VSTGS _ _ _ _).
  iApply step_fupdN_mono.
  { apply bi.pure_mono, (ext_spec_entails_safe _ (Espec HH)); auto. }
  iApply (adequacy(VSTGS0 := HH)(OK_spec := Espec HH)).
  iFrame.
  iDestruct "H" as (R) "H"; iApply "H"; last done.
  iApply guarded_stop; auto.
Qed.
