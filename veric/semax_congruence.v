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

(*
(* Some attempts to build proofs on the level of safeN. It is woarkable. But as
proofs on the level of jsafeN already existed, I will take use of that. *)
Definition safeN__cont_stronger k1 k2 :=
  forall gx vx tx w,
   (forall ora jm, m_phi jm = w ->
      @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
        gx (level w) ora (State vx tx k1) jm) ->
   (forall ora jm, m_phi jm = w ->
      @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
        gx (level w) ora (State vx tx k2) jm).

Lemma safeN__cont_stronger_suffix: forall k k1 k2,
  safeN__cont_stronger k1 k2 -> safeN__cont_stronger (k ++ k1) (k ++ k2).
Proof.
  intros; intros gx vx tx w.
  remember (level w) as n eqn:LV.
  revert gx vx tx w LV; induction n.
  + intros; apply safeN_0.
  + intros.
    specialize (H0 ora jm H1).
    rewrite safeN_step_jsem_spec in H0 |- *.
    destruct H0 as [c' [m' [? [? [? ?]]]]].

Lemma safeN__cont_stronger_suffix_aux: forall k1 k2,
*)

Definition jsafeN_equiv c1 c2 :=
  forall k1 k2,
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

(*
Definition assert_safe_equiv c1 c2 :=
  forall k1 k2,
   (forall gx vx tx,
      assert_safe Espec gx vx tx k1 (construct_rho (filter_genv gx) vx tx) =
      assert_safe Espec gx vx tx k2 (construct_rho (filter_genv gx) vx tx)) ->
   (forall gx vx tx,
      assert_safe Espec gx vx tx (Kseq c1 :: k1) (construct_rho (filter_genv gx) vx tx) =
      assert_safe Espec gx vx tx (Kseq c2 :: k2) (construct_rho (filter_genv gx) vx tx)).
*)

Definition closed_wrt_modvars_equiv c1 c2 :=
  forall F, closed_wrt_modvars c1 F <-> closed_wrt_modvars c2 F.

Definition exit_tycon_equiv c1 c2 :=
  forall Delta, exit_tycon c1 Delta = exit_tycon c2 Delta.

(*
Definition safeN__equiv c1 c2 :=
  forall k1 k2,
   (forall gx vx tx w,
     (forall ora jm, m_phi jm = w ->
        @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
          gx (level w) ora (State vx tx k1) jm) <->
     (forall ora jm, m_phi jm = w ->
        @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
          gx (level w) ora (State vx tx k2) jm)) ->
   (forall gx vx tx w,
     (forall ora jm, m_phi jm = w ->
        @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
          gx (level w) ora (State vx tx (Kseq c1 :: k1)) jm) <->
     (forall ora jm, m_phi jm = w ->
        @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
          gx (level w) ora (State vx tx (Kseq c2 :: k2)) jm)).
*)

Definition modifiedvars_equiv c1 c2 :=
  forall S, modifiedvars' c1 S = modifiedvars' c2 S.

Definition update_tycon_equiv c1 c2 :=
  forall Delta, update_tycon Delta c1 = update_tycon Delta c2.

Definition semax_equiv c1 c2 :=
  jsafeN_equiv c1 c2 /\
  modifiedvars_equiv c1 c2 /\
  update_tycon_equiv c1 c2.
(*
Lemma safeN__assert_safe_equiv: forall c1 c2,
  safeN__equiv c1 c2 -> assert_safe_equiv c1 c2.
Proof.
  unfold safeN__equiv, assert_safe_equiv.
  intros.
  specialize (H k1 k2).
  apply pred_ext''; intros.
  assert (forall (gx : genv) (vx : env) (tx : temp_env) w,
       assert_safe Espec gx vx tx k1 (construct_rho (filter_genv gx) vx tx) w <->
       assert_safe Espec gx vx tx k2 (construct_rho (filter_genv gx) vx tx) w).
  Focus 1. {
    clear - H0.
    intros gx vx tx; specialize (H0 gx vx tx).
    rewrite H0; tauto.
  } Unfocus.
  clear H0.

  unfold assert_safe in H1 |- *.
  simpl in H1 |- *.
  split.

  + unfold jsafeN, juicy_safety.safeN in H, H1 |- *.
    intros.
    apply H; clear H; [| intros; apply H0; auto | auto].
    clear - H1.
    intros; specialize (H1 gx vx tx w).
    split; intros; apply H1; auto.
  + unfold jsafeN, juicy_safety.safeN in H, H1 |- *.
    intros.
    apply H; clear H; [| intros; apply H0; auto | auto].
    clear - H1.
    intros; specialize (H1 gx vx tx w).
    split; intros; apply H1; auto.
Qed.
*)
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
  specialize (JS_EQUIV k k (fun _ _ _ _ => iff_refl _)).
  unfold assert_safe in Hc1 |- *; simpl in Hc1 |- *.
  intros ? ? _ ?.
  apply JS_EQUIV; [| assumption].
  intros.
  apply Hc1; auto.
Qed.

Lemma safeN_step_jsem_seq: forall gx vx tx n c1 c2 k ora jm,
  @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
    gx (S n) ora (State vx tx (Kseq (Ssequence c1 c2) :: k)) jm <->
  @safeN_ _ _ _ _ _ juicy_safety.Hrel (juicy_core_sem cl_core_sem) OK_spec
    gx (S n) ora (State vx tx (Kseq c1 :: Kseq c2 :: k)) jm.
Proof.
  intros.
  rewrite !safeN_step_jsem_spec.
  split; intros; destruct H as [c' [m' [? ?]]]; exists c', m'; (split; [| auto]); clear H0.
  + inversion H; subst.
    auto.
  + apply step_seq.
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
  specialize (H (H0 H1)); clear - H.
  specialize (H gx vx tx w).
  unfold jsafeN, juicy_safety.safeN in H |- *.
  split; intros.
  + destruct (level w) as [| n]; [apply safeN_0 |].
    rewrite safeN_step_jsem_seq.
    apply H with (ora := ora) (jm := jm); auto; clear - H0.
    intros.
    rewrite <- safeN_step_jsem_seq.
    apply H0; auto.
  + destruct (level w) as [| n]; [apply safeN_0 |].
    rewrite safeN_step_jsem_seq.
    apply H with (ora := ora) (jm := jm); auto; clear - H0.
    intros.
    rewrite <- safeN_step_jsem_seq.
    apply H0; auto.
Qed.

(*
Lemma safeN__equiv_seq: forall c1 c2 c3 c4,
  safeN__equiv c1 c2 ->
  safeN__equiv c3 c4 ->
  safeN__equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  unfold safeN__equiv.
  intros.
  specialize (H (Kseq c3 :: k1) (Kseq c4 :: k2)).
  specialize (H0 k1 k2).
  specialize (H (H0 H1)); clear - H.
  specialize (H gx vx tx w).
  split; intros.
  + destruct (level w) as [| n]; [apply safeN_0 |].
    rewrite safeN_step_jsem_seq.
    apply H with (ora := ora) (jm := jm); auto; clear - H0.
    intros.
    rewrite <- safeN_step_jsem_seq.
    apply H0; auto.
  + destruct (level w) as [| n]; [apply safeN_0 |].
    rewrite safeN_step_jsem_seq.
    apply H with (ora := ora) (jm := jm); auto; clear - H0.
    intros.
    rewrite <- safeN_step_jsem_seq.
    apply H0; auto.
Qed.
*)
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
Lemma Ssequence_assoc_assert_safe_equiv: forall c1 c2 c3,
  safeN__equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  unfold safeN__equiv.
  intros.
  split; intros.
  + destruct (level w) as [| n]; [apply safeN_0 |].
    rewrite !safeN_step_jsem_seq.

    
Lemma Ssequence_assoc: forall c1 c2 c3,
  semax_equiv (Ssequence c1 (Ssequence c2 c3)) (Ssequence (Ssequence c1 c2) c3).
Proof.
  intros.
*)
(*

*)
End extensions.