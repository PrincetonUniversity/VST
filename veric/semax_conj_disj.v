Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.

Open Local Scope pred.

Hint Resolve @now_later @andp_derives @sepcon_derives.

(*
Definition rmap_chain := {c: nat -> rmap | forall n, level (c n) = n /\ age (c (S n)) (c n)}.

Definition app_rmap_chain (c: rmap_chain) (n: nat) : rmap := proj1_sig c n.

Coercion app_rmap_chain: rmap_chain >-> Funclass.

Lemma rmap_chain_spec1: forall n (c: rmap_chain), level (c n) = n.
Proof.
  intros.
  destruct c; simpl.
  apply (proj1 (a n)).
Qed.

Lemma rmap_chain_spec2: forall n (c: rmap_chain), age (c (S n)) (c n).
Proof.
  intros.
  destruct c; simpl.
  apply (proj2 (a n)).
Qed.

Lemma rmap_chain_S: forall r1 r2 (c: rmap_chain) n,
  age r1 r2 ->
  c (S n) = r1 ->
  c n = r2.
Proof.
  intros.
  pose proof rmap_chain_spec2 n c.
  rewrite H0 in H1.
  unfold age in *.
  rewrite H1 in H.
  inv H; auto.
Qed.

Program Definition is_rmap_chain (c: rmap_chain): pred rmap :=
  fun r => c (level r) = r.
Next Obligation.
  hnf; intros.
  cbv beta in *.
  pose proof age_level _ _ H.
  rewrite H1 in H0.
  eapply rmap_chain_S; eauto.
Defined.

Definition exact_at (st: environ * rmap_chain): assert :=
  fun rho => !! (rho = fst st) && is_rmap_chain (snd st).
*)

Program Definition exact_at (r: rmap): pred rmap :=
  fun r' =>
  if le_lt_dec (level r') (level r) then necR r r' else False.
Next Obligation.
  hnf; simpl; intros.
  destruct (le_lt_dec (level a) (level r)).
  + pose proof age_level _ _ H.
    destruct (le_lt_dec (level a') (level r)); try omega.
    apply rt_trans with a; auto.
    apply rt_step; auto.
  + tauto.
Qed.

Lemma exact_at_spec: forall r, exact_at r r.
Proof.
  intros.
  simpl.
  if_tac; [apply necR_refl | omega].
Qed.

Lemma exact_at_rev: forall F: assert,
  F = fun rho => EX r: rmap, !! (F rho r) && exact_at r.
Proof.
  intros.
  extensionality rho.
  apply pred_ext; simpl; intros r ?.
  + exists r.
    split; [auto | apply exact_at_spec].
  + destruct H as [r0 [? ?]].
    simpl in *.
    if_tac in H0; try tauto.
    eapply pred_nec_hereditary; eauto.
Qed.

Definition exact_assert (S: ident -> Prop) (st: environ * rmap): assert :=
  fun rho =>
    !! (forall i, S i \/ Map.get (te_of rho) i = Map.get (te_of (fst st)) i) &&
    !! (ve_of rho = ve_of (fst st)) &&
    exact_at (snd st).

Lemma exact_assert_spec1: forall S st,
  closed_wrt_vars S (exact_assert S st).
Proof.
  intros.
  unfold closed_wrt_vars, exact_assert.
  intros.
  f_equal.
  apply pred_ext; unfold prop, andp, derives; simpl; intros _ [? ?]; split; auto;
  intros i;
  specialize (H i); specialize (H0 i).
  + destruct H, H0; auto; right; congruence.
  + destruct H, H0; auto; right; congruence.
Qed.

Section SemaxContext.
Context (Espec: OracleKind).

Lemma fash_imp_spec: forall (P Q: pred rmap) n, (P >=> Q) n <-> (forall w, (level w <= n)%nat -> P w -> Q w).
Proof.
  intros.
  simpl.
  split; intros.
  + apply (H w); auto.
  + apply H; auto.
    apply necR_level in H1.
    omega.
Qed.

Lemma semax_unfold' {CS: compspecs}:
  semax Espec = fun Delta P c R =>
    forall (psi: Clight.genv) Delta' (w: nat)
          (TS: tycontext_sub Delta Delta')
          (HGG: genv_cenv psi = cenv_cs)
           (Prog_OK: believe Espec Delta' psi Delta' w) (k: cont) (st: environ * rmap),
    let F := exact_assert (modifiedvars c) st in
        closed_wrt_modvars c F ->
       rguard Espec psi (exit_tycon c Delta') (frame_ret_assert R F) k w ->
       guard Espec psi Delta' (fun rho => F rho * P rho) (Kseq c :: k) w.
Proof.
  intros.
  rewrite semax_unfold.
  extensionality Delta P c R.
  apply prop_ext; split; intros; rename w into n.
  1: apply H; auto.
  specialize (H psi Delta' n TS HGG Prog_OK k).
  unfold guard.
  intros tx vx.
  rewrite fash_imp_spec.
  intros w ? ?.
  destruct H3 as [[? ?] ?].
  simpl in H3.
  destruct H4 as [w1 [w2 [? [? ?]]]].
  rewrite (exact_at_rev F) in H1.
  set (rho := construct_rho (filter_genv psi) vx tx).
  pose proof exact_assert_spec1 (modifiedvars c) (rho, w1) as SPEC1.
  assert ((rguard Espec psi (exit_tycon c Delta') (frame_ret_assert R (exact_assert (modifiedvars c) (rho, w1))) k) n) as SPEC2.
  1:{
    clear - H0 H1 H6.
    unfold rguard in *.
    intros ek vl tx' vx'.
    specialize (H1 ek vl tx' vx'); cbv beta in H1.
    rewrite fash_imp_spec in H1 |- *.
    intros w' H_LEVEL' [[? ?] ?].
    specialize (H1 w' H_LEVEL').
    apply H1.
    split; [clear H3 | auto].
    split; [auto | clear H].
    unfold frame_ret_assert in *.
    destruct H2 as [w1' [w2' [? [? ?]]]].
    exists w1', w2'; split; [auto | split; [auto |]].
    exists w1.
    split.
    + destruct H3 as [[? ?] ?].
      simpl in H3 |- *.
      unfold closed_wrt_modvars, closed_wrt_vars in H0.
      replace (F (construct_rho (filter_genv psi) vx' tx'))
        with (F (construct_rho (filter_genv psi) vx tx)); auto.
      unfold construct_rho.
      simpl in H4.
      rewrite H4.
      apply H0.
      intro i; specialize (H3 i).
      simpl.
      destruct H3; [left | right; symmetry]; auto.
    + unfold exact_assert in H3.
      destruct H3.
      auto.
  }
  specialize (H _ SPEC1 SPEC2); clear SPEC1 SPEC2.

  unfold guard in H.
  specialize (H tx vx); cbv beta in H.
  rewrite fash_imp_spec in H.
  specialize (H w H2).
  apply H.
  split; [| auto].
  split; [auto |].
  exists w1, w2; split; [auto | split; [| auto]].
  unfold exact_assert.
  split; [| apply exact_at_spec].
  split.
  + simpl. intros; right; auto.
  + simpl. auto.
Qed.

Lemma semax_conjunction {CS: compspecs} Delta (P1 P2: environ -> mpred) c Q1 Q2:
  semax Espec Delta P1 c Q1 ->
  semax Espec Delta P2 c Q2 ->
  semax Espec Delta (fun rho => P1 rho && P2 rho) c (fun k v rho => Q1 k v rho && Q2 k v rho).
Proof.
  intros.
  rewrite semax_unfold' in H, H0 |- *.
  intros.
  specialize (H psi Delta' w TS HGG Prog_OK k st H1).
  specialize (H0 psi Delta' w TS HGG Prog_OK k st H1).
  spec H.
  (* Fail. This subgoal is not provable. *)
Abort.
(*
  1:{
    clear - H2.
    unfold rguard in *.
    intros ek vl tx vx.
    specialize (H2 ek vl tx vx); cbv beta in H2.
    rewrite fash_imp_spec in H2 |- *.
    intros w' HH; specialize (H2 w' HH).
    intros; apply H2.
    unfold frame_ret_assert in *.
    destruct H as [[? ?] ?].
    split; [split |]; auto.
    clear - H0.
  replace (frame_ret_assert (fun kd v rho => Q1 kd v rho && Q2 kd v rho) F)
    with (fun kd v rho => (frame_ret_assert Q1 F) kd v rho && (frame_ret_assert Q2 F) kd v rho).
  2:{
    extensionality kd v rho.
    unfold frame_ret_assert.
    rewrite <- !(sepcon_comm (F rho)).
    Check distrib_sepcon_andp.
    SearchAbout andp sepcon.

Check semax_fold_unfold.
Check semax_fold.
    forall (psi: Clight.genv) Delta' (w: nat)
          (TS: tycontext_sub Delta Delta')
          (HGG: genv_cenv psi = cenv_cs)
           (Prog_OK: believe Espec Delta' psi Delta' w) (k: cont) (F: assert),
        closed_wrt_modvars c F ->
       rguard Espec psi (exit_tycon c Delta') (frame_ret_assert R F) k w ->
       guard Espec psi Delta' (fun rho => F rho * P rho) (Kseq c :: k) w.
*)