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
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.
Require Import Coq.Classes.RelationClasses.
(*Require Import veric.SeparationLogicSoundness. *)

Open Local Scope pred.
Open Local Scope nat_scope.

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
  @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
    gx (S n) ora (State vx tx k) jm <->
  exists c' m', (cl_step gx (State vx tx k) (m_dry jm) c' (m_dry m') /\
  resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi m') /\
  level jm = S (level m') /\
  @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec gx n ora c' m').
Proof.
  intros.
  split; intros.
  - inversion H; subst.
    * exists c', m'.
      simpl in H1.
      unfold jstep in H1.
      destruct H1 as [? [? ?]].
      simpl in H0.
      auto.
    * inversion H1.
    * inversion H0.
  - destruct H as [c' [m' [? [? [? ?]]]]].
    eapply safeN_step; [| eauto].
    simpl.
    unfold jstep.
    auto.
Qed.

Definition jsafeN_equiv c1 c2 :=
  forall k1 k2, filter_seq k1 = filter_seq k2 ->
   (forall gx vx tx w,
     (forall ora jm, m_phi jm = w ->
         jsafeN OK_spec gx (level w) ora (State vx tx k1) jm) <->
     (forall ora jm, m_phi jm = w ->
         jsafeN OK_spec gx (level w) ora (State vx tx k2) jm)) ->
   (forall gx vx tx w,
     (forall ora jm, m_phi jm = w ->
         jsafeN OK_spec gx (level w) ora (State vx tx (Kseq c1 :: k1)) jm) <->
     (forall ora jm, m_phi jm = w ->
         jsafeN OK_spec gx (level w) ora (State vx tx (Kseq c2 :: k2)) jm)).

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

Lemma semax_equiv_spec: forall c1 c2,
  semax_equiv c1 c2 ->
  (forall P Q Delta, semax Espec Delta P c1 Q -> semax Espec Delta P c2 Q).
Proof.
  rewrite semax_unfold.
  unfold semax_equiv.
  intros ? ? [JS_EQUIV [M_EQUIV U_EQUIV]] P Q Delta Hc1; intros.
  specialize (Hc1 psi Delta' w TS Prog_OK k F).

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
  specialize (JS_EQUIV k k eq_refl (fun _ _ _ _ => iff_refl _)).
  unfold assert_safe in Hc1 |- *; simpl in Hc1 |- *.
  intros ? ? _ ?.
  apply JS_EQUIV; [| assumption].
  intros.
  apply Hc1; auto.
Qed.

Lemma jsafeN_step_jsem_seq: forall gx vx tx n c1 c2 k ora jm,
  jsafeN OK_spec gx n ora (State vx tx (Kseq (Ssequence c1 c2) :: k)) jm <->
  jsafeN OK_spec gx n ora (State vx tx (Kseq c1 :: Kseq c2 :: k)) jm.
Proof.
  unfold jsafeN, juicy_safety.safeN; simpl.
  intros.
  destruct n.
  + split; intros; apply safeN_0.
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
  specialize (H H1 (H0 H1 H2)); clear - H.
  specialize (H gx vx tx w).

  split; intros.
  + rewrite jsafeN_step_jsem_seq.
    apply H with (ora := ora) (jm := jm); auto; clear - H0.
    intros.
    rewrite <- jsafeN_step_jsem_seq.
    apply H0; auto.
  + rewrite jsafeN_step_jsem_seq.
    apply H with (ora := ora) (jm := jm); auto; clear - H0.
    intros.
    rewrite <- jsafeN_step_jsem_seq.
    apply H0; auto.
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

(*
Lemma control_as_safe_jsafeN_equiv: forall c1 c2,
 (forall k1 k2,
   (forall gx n, control_as_safe Espec gx n k1 k2) /\
   (forall gx n, control_as_safe Espec gx n k2 k1) ->
   (forall gx n, control_as_safe Espec gx n (Kseq c1 :: k1) (Kseq c2 :: k2)) /\
   (forall gx n, control_as_safe Espec gx n (Kseq c2 :: k2) (Kseq c1 :: k1))) ->
  jsafeN_equiv c1 c2.
Admitted.
*)

(*
Lemma Ssequence_assoc_jsafeN_equiv: forall c1 c2 c3,
  jsafeN_equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  unfold jsafeN_equiv.
  intros.
  split; intros.
  + specialize (H1 ora jm H2).
    rewrite !jsafeN_step_jsem_seq in H1.
    rewrite !jsafeN_step_jsem_seq.
    apply (control_suffix_safe Espec gx (level w)
            (Kseq (Ssequence c2 c3) :: k1) (Kseq c2 :: Kseq c3 :: k2) (Kseq c1 :: nil));
    [simpl; auto | | auto | simpl; auto].
    unfold control_as_safe.
    intros.
    rewrite !jsafeN_step_jsem_seq in H4.
    apply (control_suffix_safe Espec gx (level w) k1 k2 (Kseq c2 :: Kseq c3 :: nil));
    [auto | | auto | simpl; auto].
    clear - H0.
    forget (level w) as n.
Print control_as_safe.
    intro; intros.
SearchAbout jsafeN.
    apply H0.
      
      
    
Lemma Ssequence_assoc: forall c1 c2 c3,
  semax_equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  intros.
*)
(*

*)
End extensions.