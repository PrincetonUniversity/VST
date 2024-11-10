(* A core wp-based separation logic for Clight, in the Iris style. Maybe VeriC can be built on top of this? *)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Cop2.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.external_state.
Require Import VST.veric.tycontext.
Require Import VST.veric.lifting_expr.

Open Scope maps.

Definition genv_symb_injective {F V} (ge: Genv.t F V) : extspec.injective_PTree Values.block.
Proof.
exists (Genv.genv_symb ge).
hnf; intros.
eapply Genv.genv_vars_inj; eauto.
Defined.

Class VSTGS OK_ty Σ :=
  { VST_heapGS :: heapGS Σ;
    VST_extGS :: externalGS OK_ty Σ }.

Section mpred.

Context `{!VSTGS OK_ty Σ} (OK_spec : ext_spec OK_ty) (ge : genv).

Lemma make_tycontext_v_lookup : forall tys id t,
  make_tycontext_v tys !! id = Some t -> In (id, t) tys.
Proof.
  intros ???; induction tys; simpl.
  - rewrite PTree.gempty //.
  - destruct a as (i, ?).
    destruct (eq_dec id i).
    + subst; rewrite PTree.gss.
      inversion 1; auto.
    + rewrite PTree.gso //; auto.
Qed.

Lemma make_tycontext_v_sound : forall tys id t, list_norepet (map fst tys) ->
  make_tycontext_v tys !! id = Some t <-> In (id, t) tys.
Proof.
  intros; split; first apply make_tycontext_v_lookup.
  induction tys; simpl; first done.
  intros [-> | ?].
  - apply PTree.gss.
  - destruct a; inv H.
    rewrite PTree.gso; auto.
    intros ->.
    contradiction H3; rewrite in_map_iff; eexists (_, _); eauto.
Qed.

Definition match_venv (ve: venviron) (vars: list (ident * type)) :=
 forall id, match ve id with Some (b,t) => In (id,t) vars | _ => True end.

Lemma typecheck_var_match_venv : forall ve tys,
  typecheck_var_environ ve (make_tycontext_v tys) → match_venv ve tys.
Proof.
  unfold typecheck_var_environ, match_venv; intros.
  destruct (ve id) as [(?, ty)|] eqn: Hid; last done.
  destruct (H id ty) as [_ Hty].
  apply make_tycontext_v_lookup, Hty; eauto.
Qed.

Definition jsafeN :=
  jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge.

Definition cont_to_state f ve te ctl :=
  match ctl with
  | Kseq s ctl' => Some (State f s ctl' ve te)
  | Kloop1 body incr ctl' => Some (State f Sskip (Kloop1 body incr ctl') ve te)
  | Kloop2 body incr ctl' => Some (State f (Sloop body incr) ctl' ve te)
  | Kcall id' f' ve' te' k' => Some (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)
  | Kstop => Some (State f (Sreturn None) Kstop ve te)
  | _ => None
  end.

Definition assert_safe (E: coPset) (f: function) (ctl: option cont) rho : iProp Σ :=
  ∀ ora ve te,
       ⌜rho = construct_rho (filter_genv ge) ve te⌝ →
       (* this is the only tycontext piece we actually need *)
       ⌜typecheck_var_environ (make_venv ve) (make_tycontext_v f.(fn_vars))⌝ →
       match option_bind _ _ (cont_to_state f ve te) ctl with
       | Some c => jsafeN E ora c
       | None => |={E}=> False
       end.

Global Instance assert_safe_absorbing E f ctl rho : Absorbing (assert_safe E f ctl rho).
Proof.
  rewrite /assert_safe.
  repeat (apply bi.forall_absorbing; intros).
  apply bi.impl_absorbing; try apply _.
  apply bi.impl_absorbing; try apply _.
  destruct (option_bind _ _ _ _); apply _.
Qed.

Lemma assert_safe_mono E1 E2 f ctl rho: E1 ⊆ E2 ->
  assert_safe E1 f ctl rho ⊢ assert_safe E2 f ctl rho.
Proof.
  rewrite /assert_safe; intros.
  iIntros "H" (??? -> ?); iSpecialize ("H" with "[%] [%]"); [done..|].
  destruct option_bind.
  - by iApply jsafe_mask_mono.
  - iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
Qed.

Lemma fupd_assert_safe : forall E f k rho,
  (|={E}=> assert_safe E f k rho) ⊢ assert_safe E f k rho.
Proof.
  intros; iIntros "H" (?????).
  iSpecialize ("H" with "[%] [%]"); [done..|].
  destruct option_bind; by iMod "H".
Qed.

Global Instance elim_modal_fupd_assert_safe p P E f c rho :
  ElimModal Logic.True p false (|={E}=> P) P (assert_safe E f c rho) (assert_safe E f c rho).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_assert_safe.
Qed.

Fixpoint break_cont (k: cont) :=
match k with
| Kseq _ k' => break_cont k'
| Kloop1 _ _ k' => Some k'
| Kloop2 _ _ k' => Some k'
| Kswitch k' => Some k'
| _ => None
end.

Fixpoint continue_cont (k: cont) :=
match k with
| Kseq _ k' => continue_cont k'
| Kloop1 s1 s2 k' => Some (Kseq s2 (Kloop2 s1 s2 k'))
| Kswitch k' => continue_cont k'
| _ => None
end.

Definition guarded E f k Q := ∀ rho,
  (RA_normal Q rho -∗ assert_safe E f (Some k) rho) ∧
  (RA_break Q rho -∗ assert_safe E f (break_cont k) rho) ∧
  (RA_continue Q rho -∗ assert_safe E f (continue_cont k) rho) ∧
  (RA_return Q None rho -∗ assert_safe E f (Some (Kseq (Sreturn None) (call_cont k))) rho) ∧
  (∀ e, wp_expr ge E e (λ v, RA_return Q (Some v)) rho -∗
          assert_safe E f (Some (Kseq (Sreturn (Some e)) (call_cont k))) rho).

Lemma fupd_guarded : forall E f k Q, (|={E}=> guarded E f k Q) ⊢ guarded E f k Q.
Proof.
  intros.
  iIntros "H" (rho); iSpecialize ("H" $! rho); repeat iSplit.
  - iMod "H" as "($ & _)".
  - iMod "H" as "(_ & $ & _)".
  - iMod "H" as "(_ & _ & $ & _)".
  - iMod "H" as "(_ & _ & _ & $ & _)".
  - iMod "H" as "(_ & _ & _ & _ & $)".
Qed.

Global Instance elim_modal_fupd_guarded p P E f k Q :
  ElimModal Logic.True p false (|={E}=> P) P (guarded E f k Q) (guarded E f k Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_guarded.
Qed.

Lemma guarded_conseq_frame : forall E f k P Q Q'
  (Hnormal : ⎡P⎤ ∗ RA_normal Q ⊢ |={E}=> RA_normal Q')
  (Hbreak : ⎡P⎤ ∗ RA_break Q ⊢ |={E}=> RA_break Q')
  (Hcontinue : ⎡P⎤ ∗ RA_continue Q ⊢ |={E}=> RA_continue Q')
  (Hreturn : ∀ v, ⎡P⎤ ∗ RA_return Q v ⊢ |={E}=> RA_return Q' v),
  P ∗ guarded E f k Q' ⊢ guarded E f k Q.
Proof.
  intros.
  iIntros "(P & H)" (rho); iSpecialize ("H" $! rho).
  repeat iSplit.
  - generalize (monPred_in_entails _ _ Hnormal rho); monPred.unseal.
    iIntros (H) "?"; iMod (H with "[$]").
    iDestruct "H" as "(H & _)"; by iApply "H".
  - generalize (monPred_in_entails _ _ Hbreak rho); monPred.unseal.
    iIntros (H) "?"; iMod (H with "[$]").
    iDestruct "H" as "(_ & H & _)"; by iApply "H".
  - generalize (monPred_in_entails _ _ Hcontinue rho); monPred.unseal.
    iIntros (H) "?"; iMod (H with "[$]").
    iDestruct "H" as "(_ & _ & H & _)"; by iApply "H".
  - generalize (monPred_in_entails _ _ (Hreturn None) rho); monPred.unseal.
    iIntros (H) "?"; iMod (H with "[$]").
    iDestruct "H" as "(_ & _ & _ & H & _)"; by iApply "H".
  - iIntros "% He"; iApply "H".
    generalize (monPred_in_entails _ _ (wp_expr_frame ge E e ⎡P⎤ (λ v, RA_return Q (Some v))) rho); rewrite monPred_at_sep.
    intros H; iPoseProof (H with "[-]") as "H".
    { monPred.unseal; iFrame. }
    rewrite wp_expr_mono //.
Qed.

Lemma guarded_conseq : forall E f k Q Q'
  (Hnormal : RA_normal Q ⊢ |={E}=> RA_normal Q')
  (Hbreak : RA_break Q ⊢ |={E}=> RA_break Q')
  (Hcontinue : RA_continue Q ⊢ |={E}=> RA_continue Q')
  (Hreturn : ∀ v, RA_return Q v ⊢ |={E}=> RA_return Q' v),
  guarded E f k Q' ⊢ guarded E f k Q.
Proof.
  intros; etrans; last apply (guarded_conseq_frame _ _ _ emp); intros; rewrite ?embed_emp bi.emp_sep //.
Qed.

Global Instance guarded_proper : forall E f k, Proper (equiv ==> equiv) (guarded E f k).
Proof.
  intros ????? (? & ? & ? & ?); rewrite /guarded.
  do 2 f_equiv.
  repeat (f_equiv; first by do 2 f_equiv).
  do 6 f_equiv; done.
Qed.

Lemma guarded_normal : forall E f k P,
  guarded E f k (normal_ret_assert P) ⊣⊢ (∀ rho, P rho -∗ assert_safe E f (Some k) rho).
Proof.
  intros.
  iSplit.
  { iIntros "H" (rho); by iDestruct ("H" $! rho) as "[? _]". }
  iIntros "H" (?); iSplit; first by iApply "H".
  simpl; monPred.unseal.
  repeat (iSplit; first by iIntros "[]").
  iIntros (?) "He".
  rewrite /wp_expr; monPred.unseal.
  iIntros (?????).
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  iMod ("He" with "[%] Hm") as ">(% & ? & ? & [])"; done.
Qed.

Definition var_sizes_ok (cenv: composite_env) (vars: list (ident*type)) :=
   Forall (fun var : ident * type => @sizeof cenv (snd var) <= Ptrofs.max_unsigned)%Z vars.

Definition var_block' (sh: Share.t) (cenv: composite_env) (idt: ident * type): assert :=
  ⌜(sizeof (snd idt) <= Ptrofs.max_unsigned)%Z⌝ ∧
  assert_of (fun rho => (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho)).

Definition stackframe_of' (cenv: composite_env) (f: Clight.function) : assert :=
  fold_right bi_sep emp
     (map (fun idt => var_block' Share.top cenv idt) (Clight.fn_vars f)).

Definition freeable_blocks: list (Values.block * BinInt.Z * BinInt.Z) -> mpred :=
  fold_right (fun bb a =>
                        match bb with (b,lo,hi) =>
                                          VALspec_range (hi-lo) Share.top (b,lo) ∗ a
                        end)
                    emp.

Lemma stackframe_of_freeable_blocks:
  forall f rho ve,
      Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f) ->
      list_norepet (map fst (fn_vars f)) ->
      ve_of rho = make_venv ve ->
      typecheck_var_environ (λ id : positive, ve !! id) (make_tycontext_v (fn_vars f)) ->
       stackframe_of' (genv_cenv ge) f rho ⊢ freeable_blocks (blocks_of_env ge ve).
Proof.
 intros until ve.
 intros COMPLETE.
 intros ???.
 assert (match_venv (make_venv ve) (fn_vars f)) as H7.
 { by apply typecheck_var_match_venv. }
 unfold stackframe_of'.
 unfold blocks_of_env.
 trans (foldr bi_sep emp (map (fun idt => var_block' Share.top (genv_cenv ge) idt rho) (fn_vars f))).
 { clear; induction (fn_vars f); simpl; auto; monPred.unseal. rewrite -IHl; by monPred.unseal. }
 unfold var_block'. unfold eval_lvar. monPred.unseal; simpl.
 rewrite H0. unfold make_venv. forget (ge_of rho) as ZZ. clear rho H0.
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
   mem_auth m ∗ stackframe_of' (genv_cenv ge) f (construct_rho (filter_genv ge) ve te) ⊢
   |==> ∃ m2, ⌜free_list m (blocks_of_env ge ve) = Some m2⌝ ∧ mem_auth m2.
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

Lemma safe_return : forall E f ora ve te (Hmatch : match_venv (make_venv ve) f.(fn_vars)),
  f.(fn_vars) = [] → (∀ m, state_interp m ora -∗ ⌜∃ i, ext_spec_exit OK_spec (Some (Vint i)) ora m⌝) ⊢ jsafeN E ora (State f (Sreturn None) Kstop ve te).
Proof.
  intros.
  iIntros "H".
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & ?)".
  rewrite H in Hmatch.
  iMod (free_stackframe f  _ ve te with "[$Hm]") as (??) "?"; rewrite ?H; try eassumption; try solve [constructor].
  { split; simpl.
    * rewrite PTree.gempty //.
    * rewrite /Map.get; intros (? & Hid).
      rewrite /match_venv /make_venv in Hmatch.
      specialize (Hmatch id); rewrite Hid // in Hmatch. }
  { rewrite /stackframe_of' H /=.
    by monPred.unseal. }
  iIntros "!>"; iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  rewrite jsafe_unfold /jsafe_pre.
  iIntros "!> !>" (?) "?"; iLeft.
  iDestruct ("H" with "[$]") as %(? & ?).
  iExists _; simpl; eauto.
Qed.

Lemma guarded_stop : forall E f (P : assert),
  f.(fn_vars) = [] →
  (∀ rho, P rho -∗ ∀ m z, state_interp m z -∗ ⌜∃ i, ext_spec_exit OK_spec (Some (Vint i)) z m⌝) ⊢
  guarded E f Kstop (function_body_ret_assert Tvoid P).
Proof.
  intros; iIntros "H" (?).
  simpl; monPred.unseal.
  iSplit.
  - iIntros "?"; rewrite /assert_safe /=.
    iIntros (??? -> ?).
    iApply safe_return.
    { by apply typecheck_var_match_venv. }
    { done. }
    iIntros (?) "?"; by iApply ("H" with "[$]").
  - do 2 (iSplit; first by iIntros "[]").
    iSplit.
    + iIntros "?"; rewrite /assert_safe /=.
      iIntros (??? -> ?).
      iApply safe_return.
      { by apply typecheck_var_match_venv. }
      { done. }
      iIntros (?) "?"; by iApply ("H" with "[$]").
    + iIntros "% He" (??? -> ?).
      iApply jsafe_step.
      rewrite /wp_expr /jstep_ex; monPred.unseal.
      iIntros (?) "(Hm & ?)".
      iMod ("He" with "[%] Hm") as ">(% & ? & ? & [] & ?)"; done.
Qed.

Definition wp E f s (Q : ret_assert) : assert :=
    assert_of (λ rho, ∀ E' k, ⌜E ⊆ E'⌝ → (* ▷ *) guarded E' f k Q -∗ assert_safe E' f (Some (Kseq s k)) rho).
(* ▷ would make sense here, but removing Kseq isn't always a step: for instance, Sskip Kstop is a synonym
   for (Sreturn None) Kstop rather than stepping to it. *)

Global Instance wp_absorbing E f s Q : Absorbing (wp E f s Q).
Proof. apply monPred_absorbing, _. Qed.

Lemma fupd_wp E f s Q : (|={E}=> wp E f s Q) ⊢ wp E f s Q.
Proof.
  split => rho; rewrite /wp; monPred.unseal.
  iIntros "H" (???) "?".
  iApply fupd_assert_safe. iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  by iMod "H"; iMod "Hclose"; iApply "H".
Qed.

Global Instance elim_modal_fupd_wp p P E f k Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp E f k Q) (wp E f k Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp.
Qed.

Global Instance is_except_0_wp E f s Q : IsExcept0 (wp E f s Q).
Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

Lemma wp_mask_mono : forall E E' f s Q (HE : E ⊆ E'),
  wp E f s Q ⊢ wp E' f s Q.
Proof.
  split => rho; rewrite /wp /=.
  iIntros "H" (???); iApply "H".
  iPureIntro; set_solver.
Qed.

(* We need R to be objective because we don't know whether s changes the environment
   in a way that affects R. We could probably fix this with env-as-resource. *)
(* Use closed_wrt_modvars instead? Probably not worth the trouble to build it
   if we're just going to tear it down later. *)
Lemma wp_frame : forall E f s Q R, ⎡R⎤ ∗ wp E f s Q ⊢ wp E f s (frame_ret_assert Q ⎡R⎤).
Proof.
  split => rho; rewrite /wp monPred_at_sep.
  iIntros "(R & H)" (???) "G".
  iApply "H"; first done.
  iApply (guarded_conseq_frame _ _ _ R); last (iFrame; monPred.unseal; iFrame);
    destruct Q; simpl; intros; iIntros "($ & $)"; done.
Qed.

(*Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Lemma wp_frame' : forall E f s Q R, closed_wrt_modvars s R →
  R ∗ wp E f s Q ⊢ wp E f s (frame_ret_assert Q R).
Proof.
  split => rho; rewrite /wp; monPred.unseal.
  iIntros "(R & H)" (???) "G".
  iApply "H"; first done.
Search modifiedvars.
  iApply (guarded_conseq_frame _ _ _ R); last (iFrame; monPred.unseal; iFrame);
    destruct Q; simpl; intros; iIntros "($ & $)"; done.
Qed.

*)

Lemma wp_conseq : forall E f s Q Q'
  (Hnormal : RA_normal Q ⊢ |={E}=> RA_normal Q')
  (Hbreak : RA_break Q ⊢ |={E}=> RA_break Q')
  (Hcontinue : RA_continue Q ⊢ |={E}=> RA_continue Q')
  (Hreturn : ∀ v, RA_return Q v ⊢ |={E}=> RA_return Q' v),
  wp E f s Q ⊢ wp E f s Q'.
Proof.
  intros.
  split => rho; rewrite /wp /=.
  iIntros "H" (???) "HG".
  rewrite guarded_conseq; first by iApply "H".
  - rewrite Hnormal; by apply fupd_mask_mono.
  - rewrite Hbreak; by apply fupd_mask_mono.
  - rewrite Hcontinue; by apply fupd_mask_mono.
  - intros; rewrite Hreturn; by apply fupd_mask_mono.
Qed.

Global Instance wp_proper E f s : Proper (equiv ==> equiv) (wp E f s).
Proof.
  split => rho; rewrite /wp /=.
  solve_proper.
Qed.

Lemma wp_seq : forall E f s1 s2 Q, wp E f s1 (overridePost (wp E f s2 Q) Q) ⊢ wp E f (Ssequence s1 s2) Q.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk" (??? -> ?).
  iApply jsafe_local_step.
  { intros; constructor. }
  iApply ("H" with "[%] [Hk]"); [done | | done..].
  iIntros (rho).
  destruct Q; simpl; iSplit; last by iDestruct ("Hk" $! rho) as "[_ $]".
  iIntros "H"; iApply "H"; auto.
Qed.

Definition valid_val v :=
  match v with Vptr _ _ => expr.valid_pointer v | _ => True end.

Definition valid_val0 m v : Prop :=
  match v with Vptr b o => valid_pointer m b (Ptrofs.intval o) = true | _ => True end.

Lemma valid_val_mem : forall m v, mem_auth m ∗ valid_val v ⊢ ⌜valid_val0 m v⌝.
Proof.
  iIntros (??) "(Hm & Hv)"; destruct v; try done.
  iApply expr_lemmas4.valid_pointer_dry0; iFrame.
Qed.

Lemma bool_val_valid : forall m v t b, valid_val0 m v -> Cop2.bool_val t v = Some b -> Cop.bool_val v t m = Some b.
Proof.
  rewrite /Cop2.bool_val /Cop.bool_val.
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
  wp_expr ge E e (λ v, ⎡valid_val v⎤ ∧ ∃ b, ⌜Cop2.bool_val (typeof e) v = Some b⌝ ∧ ▷ if b then wp E f s1 R else wp E f s2 R)
  ⊢ wp E f (Sifthenelse e s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk" (??? -> ?).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[%] Hm") as ">(% & % & Hm & H)"; first done.
  iMod "Hclose" as "_".
  iDestruct (valid_val_mem with "[Hm H]") as %?.
  { rewrite bi.and_elim_l; iFrame. }
  rewrite bi.and_elim_r; iDestruct "H" as (b ?) "H".
  iIntros "!>"; iExists _, m.
  iSplit.
  { iPureIntro.
    econstructor; eauto.
    apply bool_val_valid; eauto. }
  iFrame.
  destruct b; simpl; iNext; iApply ("H" with "[%] [-]"); done.
Qed.

(* see also semax_lemmas.derives_skip *)
Lemma safe_skip : forall E ora f k ve te (Hty : typecheck_var_environ (make_venv ve) (make_tycontext_v (fn_vars f))),
  assert_safe E f (Some k) (construct_rho (filter_genv ge) ve te) ⊢
  jsafeN E ora (State f Sskip k ve te).
Proof.
  intros; iIntros "H".
  rewrite /assert_safe.
  iSpecialize ("H" with "[%] [%]"); [done..|].
  destruct k as [ | s ctl' | | | |]; try done; try solve [iApply (jsafe_local_step with "H"); constructor].
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
  - iMod "H" as "[]".
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
Qed.

Lemma wp_skip: forall E f R, RA_normal R ⊢ wp E f Sskip R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk" (??? -> ?).
  iDestruct ("Hk" $! _) as "[Hk _]".
  by iApply safe_skip; last iApply "Hk".
Qed.

Lemma wp_set: forall E f i e R,
  wp_expr ge E e (λ v, ▷ assert_of (subst i (liftx v) (RA_normal R))) ⊢ wp E f (Sset i e) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk" (??? -> ?).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[%] Hm") as ">(% & % & Hm & H)"; first done.
  iMod "Hclose" as "_"; iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; constructor; eauto. }
  iFrame.
  iNext; simpl.
  iDestruct ("Hk" $! _) as "[Hk _]".
  iApply safe_skip; first done; last iApply "Hk".
  rewrite /subst /env_set /construct_rho /= expr_lemmas.map_ptree_rel //.
Qed.

Lemma mapsto_can_store : forall sh t ch b o v v' m (Hwrite : writable0_share sh) (Hch : access_mode t = By_value ch),
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ ⌜∃ m', Mem.store ch m b (Ptrofs.unsigned o) v' = Some m'⌝.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> if_true by auto.
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; by iApply (mapsto_can_store with "[$]").
Qed.

Lemma mapsto_store: forall t m ch v v' sh b o m' (Hsh : writable0_share sh)
  (Htc : tc_val' t v') (Hch : access_mode t = By_value ch),
  Mem.store ch m b (Ptrofs.unsigned o) v' = Some m' ->
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ |==> mem_auth m' ∗ mapsto sh t (Vptr b o) v'.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> !if_true by auto.
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; (iMod (mapsto_store _ _ _ v' with "[$]") as "[$ H]"; [done..|];
    destruct (eq_dec v' Vundef); [iRight | specialize (Htc n); iLeft]; eauto).
Qed.

Lemma wp_store: forall E f e1 e2 R,
  wp_expr ge E (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ wp_lvalue ge E e1 (λ '(b, o), let v1 := Vptr b (Ptrofs.repr o) in
    ∃ sh, ⌜writable0_share sh⌝ ∧ ⎡mapsto_ sh (typeof e1) v1⎤ ∗
    ▷ (⎡mapsto sh (typeof e1) v1 v2⎤ ={E}=∗ RA_normal R)))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H %%% Hk" (??? -> ?).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[%] Hm") as ">(% & %He2 & Hm & % & H)"; first done.
  iMod ("H" with "[%] Hm") as ">(%b & %o & % & Hm & H)"; first done.
  iDestruct "H" as (sh ?) "(Hp & H)".
  rewrite Ptrofs.repr_unsigned.
  iDestruct (mapsto_pure_facts with "Hp") as %((? & ?) & ?).
  iDestruct (mapsto_can_store with "[$Hm Hp]") as %(? & Hstore); [done.. |].
  iMod (mapsto_store with "[$Hm $Hp]") as "(Hm & Hp)"; [done.. |].
  iMod "Hclose" as "_"; iIntros "!>".
  specialize (He2 _ _ eq_refl); inv He2.
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iFrame.
  iNext.
  iApply fupd_jsafe; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[%] Hp"); first done.
  iMod "Hclose" as "_".
  by iApply safe_skip; last iApply "Hk".
  { inv H6. }
Qed.

Lemma wp_loop: forall E f s1 s2 R,
  ▷ wp E f s1 (normal_ret_assert (▷ wp E f s2 (normal_ret_assert (wp E f (Sloop s1 s2) R)))) ⊢ wp E f (Sloop s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  monPred.unseal.
  iIntros "H %%% Hk" (??? -> ?).
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[%] [Hk]"); [done | | done..].
  rewrite guarded_normal.
  iIntros (?) "H"; simpl.
  iIntros (??? -> ?).
  iApply jsafe_local_step.
  { intros; constructor; auto. }
  iNext.
  iApply ("H" with "[%] [Hk]"); [done | | done..].
  rewrite guarded_normal.
  iIntros (?) "H"; simpl.
  by iApply ("H" with "[%] Hk").
Qed.

Lemma wp_continue: forall E f R,
  RA_continue R ⊢ wp E f Scontinue R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk".
  iDestruct ("Hk" $! _) as "(_ & _ & Hk & _)".
  iSpecialize ("Hk" with "H").
  iIntros (??? -> ?); iSpecialize ("Hk" with "[%] [%]"); [done..|].
  destruct (continue_cont k) eqn:Hcont; simpl; last by iMod "Hk" as "[]".
  rename c into k'.
  assert (exists s c, k' = Kseq s c) as (? & ? & Hcase).
  { induction k; inv Hcont; eauto. }
  rewrite Hcase.
  iInduction k as [| | | | |] "IHk" forall (k' Hcont Hcase); try discriminate.
  - iApply jsafe_local_step.
    { constructor. }
    iApply ("IHk" with "[%] [%] Hk"); eauto.
  - inv Hcont.
    iApply jsafe_local_step.
    { intros; apply step_skip_or_continue_loop1; auto. }
    iApply "Hk".
  - iApply jsafe_local_step.
    { apply step_continue_switch. }
    iApply ("IHk" with "[%] [%] Hk"); eauto.
Qed.

Lemma wp_break: forall E f R,
  RA_break R ⊢ wp E f Sbreak R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk".
  iDestruct ("Hk" $! _) as "(_ & Hk & _)".
  iSpecialize ("Hk" with "H").
  iIntros (??? -> ?); iSpecialize ("Hk" with "[%] [%]"); [done..|].
  destruct (break_cont k) eqn: Hcont; simpl; last by iMod "Hk" as "[]".
  destruct c; simpl; try iMod "Hk" as "[]".
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
  ∀ m, ⎡mem_auth m⎤ -∗
         ∃ vs, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_exprlist ge ve te m es ts vs (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡mem_auth m⎤ ∗ Φ vs.

Lemma alloc_vars_lookup :
forall ge id m1 l ve m2 e ,
list_norepet (map fst l) ->
(forall i, In i (map fst l) -> e !! i = None) ->
Clight.alloc_variables ge (e) m1 l ve m2 ->
(exists v, e !! id = Some v) ->
ve !! id = e !! id.
Proof.
intros.
generalize dependent e.
revert ve m1 m2.

induction l; intros.
inv H1. auto.

inv H1. simpl in *. inv H.
destruct H2.
assert (id <> id0).
intro. subst.  specialize (H0 id0). spec H0. auto. rewrite H // in H0.
eapply IHl in H10.
rewrite Maps.PTree.gso in H10; auto.
auto. intros. rewrite Maps.PTree.gsspec. if_tac. subst. tauto.
apply H0. auto.
rewrite Maps.PTree.gso; auto. eauto.
Qed.

Lemma alloc_vars_lemma : forall ge id ty l m1 m2 ve ve'
(SD : forall i, In i (map fst l) -> ve !! i = None),
list_norepet (map fst l) ->
Clight.alloc_variables ge ve m1 l ve' m2 ->
(In (id, ty) l ->
exists v, ve' !! id = Some (v, ty)).
Proof.
  intros.
  generalize dependent ve.
  revert m1 m2.
  induction l; intros; first done.
  destruct a; simpl in *.
  destruct H1 as [[=] | H1].
  - subst. inv H0. inv H. apply alloc_vars_lookup with (id := id) in H9; auto.
    rewrite H9. rewrite Maps.PTree.gss. eauto.
    { intros. destruct (peq i id); first by subst; tauto. rewrite Maps.PTree.gso; eauto. }
    { rewrite Maps.PTree.gss; eauto. }
  - inv H0. inv H. apply IHl in H10; auto.
    intros. rewrite Maps.PTree.gsspec. if_tac; last eauto. subst; done.
Qed.

Lemma alloc_vars_match_venv_gen: forall ge ve m l0 l ve' m',
  match_venv (make_venv ve) l0 ->
  Clight.alloc_variables ge ve m l ve' m' ->
  match_venv (make_venv ve') (l0 ++ l).
Proof.
  intros.
  generalize dependent l0; induction H0; intros.
  { rewrite app_nil_r //. }
  specialize (IHalloc_variables (l0 ++ [(id, ty)])).
  rewrite -assoc in IHalloc_variables; apply IHalloc_variables.
  rewrite /match_venv /make_venv in H1 |- *; intros i; specialize (H1 i).
  destruct (eq_dec i id).
  - subst; rewrite Maps.PTree.gss in_app; simpl; auto.
  - rewrite Maps.PTree.gso //.
    destruct (Maps.PTree.get i e) as [(?, ?)|]; first rewrite in_app; simpl; auto.
Qed.

Lemma alloc_vars_match_venv: forall ge m l ve' m',
  Clight.alloc_variables ge empty_env m l ve' m' ->
  match_venv (make_venv ve') l.
Proof.
  intros; eapply (alloc_vars_match_venv_gen _ _ _ []) in H; auto.
  rewrite /match_venv /make_venv; intros.
  rewrite Maps.PTree.gempty //.
Qed.

Lemma alloc_vars_typecheck_environ : forall m l ve' m',
  list_norepet (map fst l) ->
  Clight.alloc_variables ge empty_env m l ve' m' ->
  typecheck_var_environ (make_venv ve') (make_tycontext_v l).
Proof.
  intros ????? Halloc.
  rewrite /typecheck_var_environ /=; intros.
  rewrite make_tycontext_v_sound //.
  rewrite /Map.get /make_venv.
  split.
  + intros; eapply alloc_vars_lemma; eauto.
    intros; apply Maps.PTree.gempty.
  + intros (? & Hi); apply alloc_vars_match_venv in Halloc.
    rewrite /match_venv /make_venv in Halloc.
    specialize (Halloc id); rewrite Hi // in Halloc.
Qed.

Lemma alloc_block:
 forall m n m' b (Halloc : Mem.alloc m 0 n = (m', b))
   (Hn : 0 <= n < Ptrofs.modulus),
   mem_auth m ⊢ |==> mem_auth m' ∗ memory_block Share.top n (Vptr b Ptrofs.zero).
Proof.
  intros.
  iIntros "Hm"; iMod (mapsto_alloc_bytes with "Hm") as "($ & H)"; first done; iIntros "!>".
  rewrite /memory_block Ptrofs.unsigned_zero.
  iSplit; first by iPureIntro; lia.
  rewrite Z.sub_0_r memory_block'_eq; [| lia..].
  rewrite /memory_block'_alt if_true; last auto.
  rewrite /VALspec_range Nat2Z.id.
  iApply (big_sepL_mono with "H"); intros.
  rewrite address_mapsto_VALspec_range /= VALspec1 //.
Qed.

Lemma alloc_stackframe:
  forall m f te
      (COMPLETE: Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f))
      (Hsize: Forall (fun var => @Ctypes.sizeof ge (snd var) <= Ptrofs.max_unsigned) (fn_vars f)),
      list_norepet (map fst (fn_vars f)) ->
      mem_auth m ⊢ |==> ∃ m' ve, ⌜Clight.alloc_variables ge empty_env m (fn_vars f) ve m' ∧ typecheck_var_environ (make_venv ve) (make_tycontext_v (fn_vars f))⌝ ∧
        mem_auth m' ∗ stackframe_of' (genv_cenv ge) f (construct_rho (filter_genv ge) ve te).
Proof.
  intros.
  cut (mem_auth m ⊢ |==> ∃ (m' : Memory.mem) (ve : env),
    ⌜(∀i, sub_option (empty_env !! i)%maps (ve !! i)%maps) ∧ alloc_variables ge empty_env m (fn_vars f) ve m'⌝
    ∧ mem_auth m' ∗ stackframe_of' (genv_cenv ge) f (construct_rho (filter_genv ge) ve te)).
  { intros Hgen; rewrite Hgen; iIntros ">(% & % & (% & %) & ?) !>".
    iExists _, _; iFrame; iPureIntro; split3; split; auto.
    eapply alloc_vars_typecheck_environ; eauto. }
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

Lemma build_call_temp_env:
  forall f vl,
     length (fn_params f) = length vl ->
  exists te,  bind_parameter_temps (fn_params f) vl
                     (create_undef_temps (fn_temps f)) = Some te.
Proof.
 intros.
 forget (create_undef_temps (fn_temps f)) as rho.
 revert rho vl H; induction (fn_params f); destruct vl; intros; inv H; try congruence.
 exists rho; reflexivity.
 destruct a; simpl.
 apply IHl. auto.
Qed.

Lemma wp_call: forall E f0 e es R,
  wp_expr ge E e (λ v, ∃ f, ⌜exists b, v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr ge b = Some (Internal f) /\
    classify_fun (typeof e) =
    fun_case_f (type_of_params (fn_params f)) (fn_return f) (fn_callconv f) /\
    Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst f.(fn_params) ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok (genv_cenv ge) (f.(fn_vars))⌝ ∧
    wp_exprs es (type_of_params (fn_params f)) (λ vs, ⌜length vs = length f.(fn_params)⌝ ∧ ▷ assert_of (λ rho,
      ∀ rho', stackframe_of' (genv_cenv ge) f rho' -∗ ▷ wp E f f.(fn_body) (normal_ret_assert (assert_of (λ rho'', stackframe_of' (genv_cenv ge) f rho'' ∗ RA_normal R rho))) rho'))) ⊢
  wp E f0 (Scall None e es) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H %%% Hk" (??? -> ?).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr /wp_exprs.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[%] Hm") as ">(% & %He & Hm & %f & %Hb & H)"; first done.
  destruct Hb as (b & -> & Hb & ? & ? & ? & ? & ?).
  iDestruct ("H" with "[%] Hm") as (vs Hes) "(Hm & % & H)"; first done.
  iMod "Hclose" as "_"; iIntros "!>".
  specialize (He _ _ eq_refl).
  specialize (Hes _ _ _ eq_refl).
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_step.
  rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  destruct (build_call_temp_env f vs) as (le & ?); first done.
  iMod (alloc_stackframe with "Hm") as (m' ve' (? & ?)) "(Hm & Hstack)"; [done..|].
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto.
    * eapply list_norepet_append_left; eauto.
    * apply list_norepet_append_inv; auto. }
  iFrame.
  iApply ("H" with "[$] [%] [Hk]"); [done | | done..].
  rewrite guarded_normal.
  iIntros "!>" (?) "(? & HR)".
  iIntros (??? -> ?).
  iApply jsafe_step.
  rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  iMod (free_stackframe with "[$]") as (m'' ?) "Hm"; [done..|].
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  simpl.
  iApply safe_skip; last iApply "Hk"; done.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros; simpl; auto.
Qed.

Lemma wp_return_Some: forall E f e R,
  wp_expr ge E e (λ v, RA_return R (Some v)) ⊢ wp E f (Sreturn (Some e)) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk" (??? -> ?).
  iApply (convergent_controls_jsafe _ _ _ (State f (Sreturn (Some e)) (call_cont k) ve te)); try done.
  { inversion 1; subst; try match goal with H : _ \/ _ |- _ => destruct H; done end.
    rewrite call_cont_idem; econstructor; eauto. }
  iDestruct ("Hk" $! _) as "(_ & _ & _ & _ & Hk)".
  rewrite wp_expr_mask_mono //.
  iSpecialize ("Hk" with "H").
  by iApply "Hk".
Qed.

Lemma wp_return_None: forall E f R,
  RA_return R None ⊢ wp E f (Sreturn None) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk" (??? -> ?).
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
  rewrite /state_interp /mem_auth /funspec_auth /=; iFrame.
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
  ge m z f s (R : forall `{!VSTGS OK_ty Σ}, assert) ve te (Hf : f.(fn_vars) = [])
  (EXIT: forall `{!VSTGS OK_ty Σ}, ⊢ (∀ rho, R rho -∗ ∀ m z, state_interp m z -∗ ⌜∃ i, ext_spec_exit Espec (Some (Vint i)) z m⌝)),
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ in
    local (λ rho, rho = construct_rho (filter_genv ge) ve te) ∧ ⌜typecheck_var_environ (make_venv ve) (make_tycontext_v f.(fn_vars))⌝ ∧ ⎡state_interp m z⎤ ∗ wp Espec ge ⊤ f s (function_body_ret_assert Tvoid R)) →
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
  iIntros "(% & % & S & H)".
  iApply step_fupd_intro; first done.
  iNext.
  set (HH := Build_VSTGS _ _ _ _).
  iApply step_fupdN_mono.
  { apply bi.pure_mono, (ext_spec_entails_safe _ (Espec HH)); auto. }
  iApply (adequacy(VSTGS0 := HH)(OK_spec := Espec HH)).
  iFrame.
  iApply "H"; [done | | done..].
  iApply guarded_stop; auto.
  iApply EXIT.
Qed.
