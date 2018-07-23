Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.seplog.
Require Import VST.veric.assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.
Require Import Coq.Classes.RelationClasses.
Require Import VST.veric.own.

Local Open Scope pred.
Local Open Scope nat_scope.

Lemma pred_ext'': forall {A} {agA: ageable A} (P Q: pred A),
  (forall w: A, P w <-> Q w) <-> P = Q.
Proof.
  intros.
  split; intros.
  + apply pred_ext; intro w; rewrite H; auto.
  + rewrite H.
    reflexivity.
Qed.

Section extensions.
Context (Espec : OracleKind).

Lemma safeN_step_jsem_spec: forall gx vx tx n k ora jm,
  @jsafeN_ _ _ _ (fun x => genv_symb_injective (genv_genv x)) (cl_core_sem gx) OK_spec
    gx (S n) ora (State vx tx k) jm <->
  exists c' m', (cl_step gx (State vx tx k) (m_dry jm) c' (m_dry m') /\
  resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi m') /\
  level jm = S (level m') /\
  ghost_of (m_phi m') = ghost_approx m' (ghost_of (m_phi jm)) /\
  jm_bupd ora (@jsafeN_ _ _ _ (fun x => genv_symb_injective (genv_genv x)) (cl_core_sem gx) OK_spec gx n ora c') m').
Proof.
  intros.
  split; intros.
  - inversion H; subst.
    * exists c', m'.
      simpl in H1.
      unfold jstep in H1.
      destruct H1 as [? [? []]].
      simpl in H0.
      auto.
    * inversion H1.
    * inversion H0.
  - destruct H as [c' [m' [? [? [? [? ?]]]]]].
    eapply jsafeN_step; [| eauto].
    simpl.
    unfold jstep.
    auto.
Qed.

Definition jsafeN_equiv c1 c2 :=
  forall k1 k2, filter_seq k1 = filter_seq k2 ->
   (forall gx vx tx n ora jm,
     (jsafeN OK_spec gx n ora (State vx tx k1) jm <->
      jsafeN OK_spec gx n ora (State vx tx k2) jm)) ->
   (forall gx vx tx n ora jm,
     (jsafeN OK_spec gx n ora (State vx tx (Kseq c1 :: k1)) jm <->
      jsafeN OK_spec gx n ora (State vx tx (Kseq c2 :: k2)) jm)).

Definition closed_wrt_modvars_equiv c1 c2 :=
  forall F, closed_wrt_modvars c1 F <-> closed_wrt_modvars c2 F.

Definition exit_tycon_equiv c1 c2 :=
  forall Delta, exit_tycon c1 Delta = exit_tycon c2 Delta.

Definition modifiedvars_equiv c1 c2 :=
  forall S, modifiedvars' c1 S = modifiedvars' c2 S.

Definition update_tycon_equiv c1 c2 :=
  forall Delta, update_tycon Delta c1 = update_tycon Delta c2.

Definition semax_equiv c1 c2 :=
  jsafeN_equiv c1 c2 /\
  modifiedvars_equiv c1 c2 /\
  update_tycon_equiv c1 c2.

Lemma modifiedvars_closed_wrt_modvars_equiv: forall c1 c2,
  modifiedvars_equiv c1 c2 -> closed_wrt_modvars_equiv c1 c2.
Proof.
  unfold closed_wrt_modvars_equiv, modifiedvars_equiv.
  unfold closed_wrt_modvars, modifiedvars.
  intros.
  rewrite H.
  tauto.
Qed.

Lemma update_tycon_exit_tycon_equiv: forall c1 c2,
  update_tycon_equiv c1 c2 -> exit_tycon_equiv c1 c2.
Proof.
  unfold update_tycon_equiv, exit_tycon_equiv.
  intros.
  extensionality ek.
  destruct ek; auto.
  simpl.
  rewrite H; reflexivity.
Qed.

Lemma semax_equiv_spec{CS: compspecs}: forall c1 c2,
  semax_equiv c1 c2 ->
  (forall P Q Delta, semax Espec Delta P c1 Q -> semax Espec Delta P c2 Q).
Proof.
  rewrite semax_unfold.
  unfold semax_equiv.
  intros ? ? [JS_EQUIV [M_EQUIV U_EQUIV]] P Q Delta Hc1; intros.
  specialize (Hc1 psi Delta' w TS HGG Prog_OK k F).

  apply modifiedvars_closed_wrt_modvars_equiv in M_EQUIV.
  specialize (M_EQUIV F).
  spec Hc1; [clear - M_EQUIV H; tauto |].

  apply update_tycon_exit_tycon_equiv in U_EQUIV.
  specialize (U_EQUIV Delta').
  spec Hc1; [rewrite <- U_EQUIV in H0; auto |].

  clear - JS_EQUIV Hc1.
  unfold guard in Hc1 |- *.
  intros te ve ? ? ? ? ?.
  specialize (Hc1 te ve y H a' H0 H1).
    (* This step uses that fact that current function has nothing to do with c1 and c2. *)
  clear - JS_EQUIV Hc1.
  specialize (JS_EQUIV k k eq_refl (fun _ _ _ _ _ _ => iff_refl _)).
  eapply bupd_mono, Hc1.
  clear Hc1; intros ? Hc1.
  intros ? ? _ ?.
  apply JS_EQUIV.
  apply Hc1; auto.
Qed.

Lemma jsafeN_step_jsem_seq: forall gx vx tx n c1 c2 k ora jm,
  jsafeN OK_spec gx n ora (State vx tx (Kseq (Ssequence c1 c2) :: k)) jm <->
  jsafeN OK_spec gx n ora (State vx tx (Kseq c1 :: Kseq c2 :: k)) jm.
Proof.
  unfold jsafeN; simpl.
  intros.
  destruct n.
  + split; intros; apply jsafeN_0.
  + rewrite !safeN_step_jsem_spec.
    split; intros; destruct H as [c' [m' [? ?]]]; exists c', m'; (split; [| auto]); clear H0.
    - inversion H; subst.
      auto.
    - apply step_seq.
      auto.
Qed.

Lemma jsafeN_equiv_seq: forall c1 c2 c3 c4,
  jsafeN_equiv c1 c2 ->
  jsafeN_equiv c3 c4 ->
  jsafeN_equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  unfold jsafeN_equiv.
  intros.
  specialize (H (Kseq c3 :: k1) (Kseq c4 :: k2)).
  specialize (H0 k1 k2).
  specialize (H H1 (H0 H1 H2)).
  specialize (H gx vx tx n ora jm).
  clear - H.

  rewrite !jsafeN_step_jsem_seq.
  auto.
Qed.

Lemma modifiedvars_equiv_seq: forall c1 c2 c3 c4,
  modifiedvars_equiv c1 c2 ->
  modifiedvars_equiv c3 c4 ->
  modifiedvars_equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  unfold modifiedvars_equiv.
  intros.
  simpl.
  rewrite H0, H.
  reflexivity.
Qed.

Lemma update_tycon_equiv_seq: forall c1 c2 c3 c4,
  update_tycon_equiv c1 c2 ->
  update_tycon_equiv c3 c4 ->
  update_tycon_equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  unfold update_tycon_equiv.
  intros.
  simpl.
  rewrite H0, H.
  reflexivity.
Qed.

Lemma semax_equiv_seq: forall c1 c2 c3 c4,
  semax_equiv c1 c2 ->
  semax_equiv c3 c4 ->
  semax_equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  unfold semax_equiv.
  intros.
  split; [| split].
  + apply jsafeN_equiv_seq; tauto.
  + apply modifiedvars_equiv_seq; tauto.
  + apply update_tycon_equiv_seq; tauto.
Qed.

Lemma Ssequence_assoc_jsafeN_equiv: forall c1 c2 c3,
  jsafeN_equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  unfold jsafeN_equiv.
  intros.
  split; intros.
  + rewrite !jsafeN_step_jsem_seq in H1.
    rewrite !jsafeN_step_jsem_seq.
    apply (control_suffix_safe Espec gx n
            (Kseq (Ssequence c2 c3) :: k1) (Kseq c2 :: Kseq c3 :: k2) (Kseq c1 :: nil));
    [simpl; auto | | auto | simpl; exact H1].
    clear ora vx tx jm H1.
    unfold control_as_safe.
    intros ora vx tx jm n' ? ?.
    rewrite !jsafeN_step_jsem_seq in H2.
    apply (control_suffix_safe Espec gx n' k1 k2 (Kseq c2 :: Kseq c3 :: nil));
    [auto | | auto | simpl; exact H2].
    clear ora vx tx jm n H1 H2.
    unfold control_as_safe.
    intros ora vx tx jm n ? ?.
    apply H0; auto.
  + rewrite !jsafeN_step_jsem_seq in H1.
    rewrite !jsafeN_step_jsem_seq.
    apply (control_suffix_safe Espec gx n
            (Kseq c2 :: Kseq c3 :: k2) (Kseq (Ssequence c2 c3) :: k1) (Kseq c1 :: nil));
    [simpl; auto | | auto | simpl; exact H1].
    clear ora vx tx jm H1.
    unfold control_as_safe.
    intros ora vx tx jm n' ? ?.
    rewrite !jsafeN_step_jsem_seq.
    apply (control_suffix_safe Espec gx n' k2 k1 (Kseq c2 :: Kseq c3 :: nil));
    [auto | | auto | simpl; exact H2].
    clear ora vx tx jm n H1 H2.
    unfold control_as_safe.
    intros ora vx tx jm n ? ?.
    apply H0; auto.
Qed.

Lemma Ssequence_assoc_modifiedvars_equiv: forall c1 c2 c3,
  modifiedvars_equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  unfold modifiedvars_equiv.
  intros.
  reflexivity.
Qed.

Lemma Ssequence_assoc_update_tycon_equiv: forall c1 c2 c3,
  update_tycon_equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  unfold update_tycon_equiv.
  intros.
  reflexivity.
Qed.

Lemma Ssequence_assoc_semax_equiv: forall c1 c2 c3,
  semax_equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  intros.
  split; [| split].
  + apply Ssequence_assoc_jsafeN_equiv.
  + apply Ssequence_assoc_modifiedvars_equiv.
  + apply Ssequence_assoc_update_tycon_equiv.
Qed.

Lemma semax_equiv_refl: forall c, semax_equiv c c.
Proof.
  intros.
  split; [| split].
  + intro; intros.
    split.
    - apply (control_suffix_safe Espec gx n k1 k2 (Kseq c :: nil)); auto.
      intro; intros.
      apply H0; auto.
    - apply (control_suffix_safe Espec gx n k2 k1 (Kseq c :: nil)); auto.
      intro; intros.
      apply H0; auto.
  + intro; intros.
    reflexivity.
  + intro; intros.
    reflexivity.
Qed.

Lemma semax_equiv_sym: forall c1 c2, semax_equiv c1 c2 -> semax_equiv c2 c1.
Proof.
  intros.
  destruct H as [? [? ?]].
  split; [| split].
  + intro; intros.
    symmetry.
    apply H; auto.
    intros.
    symmetry.
    apply H3.
  + intro; intros.
    symmetry.
    apply H0.
  + intro; intros.
    symmetry.
    apply H1.
Qed.

Lemma semax_equiv_trans: forall c1 c2 c3, semax_equiv c1 c2 -> semax_equiv c2 c3 -> semax_equiv c1 c3.
Proof.
  intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  split; [| split].
  + intro; intros.
    rewrite (H k1 k1), (H0 k1 k2); auto.
    - reflexivity.
    - intros; reflexivity.
  + intro; intros.
    rewrite H1, H3.
    reflexivity.
  + intro; intros.
    rewrite H2, H4.
    reflexivity.
Qed.

Fixpoint unfold_Ssequence c :=
  match c with
  | Ssequence c1 c2 => unfold_Ssequence c1 ++ unfold_Ssequence c2
  | _ => c :: nil
  end.

Fixpoint fold_Ssequence lc :=
  match lc with
  | nil => Sskip
  | c1 :: nil => c1
  | c :: lc0 => Ssequence c (fold_Ssequence lc0)
  end.

Definition non_Sseq c :=
  match c with
  | Ssequence _ _ => False
  | _ => True
  end.

Inductive unfold_Sseq_rel: statement -> list statement -> Prop :=
  | singleton: forall c, non_Sseq c -> unfold_Sseq_rel c (c :: nil)
  | tl_step: forall c1 c2 lc, non_Sseq c1 -> unfold_Sseq_rel c2 lc ->
                 unfold_Sseq_rel (Ssequence c1 c2) (c1 :: lc)
  | hd_step: forall c1 c2 c3 lc, unfold_Sseq_rel (Ssequence c1 (Ssequence c2 c3)) lc ->
                 unfold_Sseq_rel (Ssequence (Ssequence c1 c2) c3) lc
  .

Lemma unfold_Sseq_rel_non_nil: forall {c} {P: Prop}, unfold_Sseq_rel c nil -> P.
Proof.
  intros.
  remember nil as lc.
  induction H.
  + congruence.
  + congruence.
  + auto.
Qed.

Lemma unfold_Sseq_rel_sound: forall c lc,
  unfold_Sseq_rel c lc -> semax_equiv (fold_Ssequence lc) c.
Proof.
  intros.
  induction H.
  + simpl.
    apply semax_equiv_refl.
  + simpl.
    destruct lc; [apply (unfold_Sseq_rel_non_nil H0) |].
    apply semax_equiv_seq; [apply semax_equiv_refl | assumption].
  + eapply semax_equiv_trans; [eauto |].
    apply Ssequence_assoc_semax_equiv.
Qed.

Lemma unfold_Ssequence_unfold_Sseq_rel: forall c, unfold_Sseq_rel c (unfold_Ssequence c).
Proof.
  intros.
  induction c; try solve [apply singleton, I].
  revert c2 IHc2.
  clear IHc1.
  induction c1; intros; try solve [apply tl_step; [apply I | auto]].
  apply hd_step.
  replace (unfold_Ssequence (Ssequence (Ssequence c1_1 c1_2) c2)) with
    (unfold_Ssequence (Ssequence c1_1 (Ssequence c1_2 c2))).
  Focus 2. {
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  } Unfocus.
  apply IHc1_1.
  apply IHc1_2.
  apply IHc2.
Qed.

Lemma unfold_Ssequence_sound: forall c, semax_equiv (fold_Ssequence (unfold_Ssequence c)) c.
Proof.
  intros.
  apply unfold_Sseq_rel_sound.
  apply unfold_Ssequence_unfold_Sseq_rel.
Qed.

Lemma semax_unfold_Ssequence {CS: compspecs}: forall c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q Delta, semax Espec Delta P c1 Q -> semax Espec Delta P c2 Q).
Proof.
  intros.
  eapply semax_equiv_spec; eauto.
  eapply semax_equiv_trans.
  + apply semax_equiv_sym.
    apply unfold_Ssequence_sound.
  + rewrite H.
    apply unfold_Ssequence_sound.
Qed.

End extensions.