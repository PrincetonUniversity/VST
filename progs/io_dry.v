Require Import VST.progs.io_specs.
Require Import VST.progs.io.
Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.veric.SequentialClight.
Require Import VST.progs.conclib.
Require Import VST.progs.dry_mem_lemmas.
Require Import ITree.ITree.
(* Import ITreeNotations. *) (* one piece conflicts with subp notation *)
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Section IO_Dry.

Definition getchar_pre (m : mem) (witness : int -> IO_itree) (z : IO_itree) :=
  let k := witness in (eutt eq z (r <- read;; k r)).

Definition getchar_post (m0 m : mem) r (witness : int -> IO_itree) (z : IO_itree) :=
  m0 = m /\ - two_p 7 <= Int.signed r <= two_p 7 - 1 /\ let k := witness in z = k r.

Definition putchar_pre (m : mem) (witness : int * IO_itree) (z : IO_itree) :=
  let '(c, k) := witness in (eutt eq z (write c;; k)).

Definition putchar_post (m0 m : mem) r (witness : int * IO_itree) (z : IO_itree) :=
  m0 = m /\ let '(c, k) := witness in r = c /\ z = k.

Context (ext_link : String.string -> ident).

Instance Espec : OracleKind := IO_Espec ext_link.

Definition io_ext_spec := OK_spec.

Program Definition io_dry_spec : external_specification mem external_function IO_itree.
Proof.
  unshelve econstructor.
  - intro e.
    pose (ext_spec_type io_ext_spec e) as T; simpl in T.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|exact False]];
      match goal with T := (_ * ?A)%type |- _ => exact (mem * A)%type end.
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ putchar_pre X3 w X2).
    + destruct X as (m0 & _ & w).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ getchar_pre X3 w X2).
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (putchar_post m0 X3 i w X2).
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (getchar_post m0 X3 i w X2).
  - intros; exact False.
Defined.

Definition dessicate : forall ef (jm : juicy_mem), ext_spec_type io_ext_spec ef -> ext_spec_type io_dry_spec ef.
Proof.
  simpl; intros.
  destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|assumption]].
  - destruct X as [_ X]; exact (m_dry jm, X).
  - destruct X as [_ X]; exact (m_dry jm, X).
Defined.

Theorem juicy_dry_specs : juicy_dry_ext_spec _ io_ext_spec io_dry_spec dessicate.
Proof.
  split; [|split]; try reflexivity; simpl.
  - unfold funspec2pre, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct t as (? & ? & (c, k)); simpl in *.
      destruct H1 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold getchar_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      symmetry.
      eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | apply join_comm, core_unit]; subst; auto.
    + unfold funspec2pre; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct t as (? & ? & k); simpl in *.
      destruct H2 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold putchar_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      unfold getchar_pre.
      symmetry.
      eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | apply join_comm, core_unit]; subst; auto.
  - unfold funspec2pre, funspec2post, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct H0 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & (c, k)); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (Hmem & ? & ?); subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost k, NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      split; [|split3].
      * eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * split3; simpl.
        -- split; auto.
        -- split; auto; split; unfold liftx; simpl; unfold lift.lift; auto; discriminate.
        -- unfold SEPx; simpl.
             rewrite seplog.sepcon_emp.
             unfold ITREE; exists k; split; [apply Reflexive_eutt|].
             eapply age_to.age_to_pred, change_has_ext; eauto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H3; eexists; constructor; constructor.
        instantiate (1 := (_, _)).
        constructor; simpl; [|constructor; auto].
        apply ext_ref_join.
    + unfold funspec2pre, funspec2post, dessicate; simpl.
      if_tac; [|contradiction].
      clear H0.
      intros; subst.
      destruct H0 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & k); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as (_ & _ & ? & ? & Htrace).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (Hmem & ? & Hw); simpl in Hw; subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost (k i), NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      split; [|split3].
      * eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * exists i.
        split3; simpl.
        -- split; auto.
        -- split; auto; split; unfold liftx; simpl; unfold lift.lift; auto; discriminate.
        -- unfold SEPx; simpl.
             rewrite seplog.sepcon_emp.
             unfold ITREE; exists (k i); split; [apply Reflexive_eutt|].
             eapply age_to.age_to_pred, change_has_ext; eauto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H3; eexists; constructor; constructor.
        instantiate (1 := (_, _)).
        constructor; simpl; [|constructor; auto].
        apply ext_ref_join.
Qed.

Instance mem_evolve_refl : Reflexive mem_evolve.
Proof.
  repeat intro.
  destruct (access_at x loc Cur); auto.
  destruct p; auto.
Qed.

Lemma dry_spec_mem : ext_spec_mem_evolve _ io_dry_spec.
Proof.
  intros ??????????? Hpre Hpost.
  simpl in Hpre, Hpost.
  simpl in *.
  if_tac in Hpre.
  - destruct w as (m0 & _ & w).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost; subst.
    reflexivity.
  - if_tac in Hpre; [|contradiction].
    destruct w as (m0 & _ & w).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost; subst.
    reflexivity.
Qed.

End IO_Dry.
