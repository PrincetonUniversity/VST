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

Section IO_Dry.

Context {E : Type -> Type} {IO_E : @IO_event nat -< E}.

Definition getchar_pre (m : mem) (witness : byte -> IO_itree) (z : IO_itree) :=
  let k := witness in (sutt eq (r <- read stdin;; k r) z).

Definition getchar_post (m0 m : mem) (r : int) (witness : byte -> IO_itree) (z : IO_itree) :=
  m0 = m /\ -1 <= Int.signed r <= Byte.max_unsigned /\
  let k := witness in if eq_dec (Int.signed r) (-1) then sutt eq (r <- read stdin;; k r) z else z = k (Byte.repr (Int.signed r)).

Definition putchar_pre (m : mem) (witness : byte * IO_itree) (z : IO_itree) :=
  let '(c, k) := witness in (sutt eq (write stdout c;; k) z).

Definition putchar_post (m0 m : mem) (r : int) (witness : byte * IO_itree) (z : IO_itree) :=
  m0 = m /\ let '(c, k) := witness in
  (Int.signed r = -1 \/ Int.signed r = Byte.unsigned c) /\
  if eq_dec (Int.signed r) (-1) then sutt eq (write stdout c;; k) z else z = k.

Context (ext_link : String.string -> ident).

Instance Espec : OracleKind := IO_Espec ext_link.

Definition io_ext_spec := OK_spec.

Program Definition io_dry_spec : external_specification mem external_function (@IO_itree E).
Proof.
  unshelve econstructor.
  - intro e.
    pose (ext_spec_type io_ext_spec e) as T; simpl in T.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|exact False]];
      match goal with T := (_ * ?A)%type |- _ => exact (mem * A)%type end.
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      exact (X1 = [Vubyte (fst w)] /\ m0 = X3 /\ putchar_pre X3 w X2).
    + destruct X as (m0 & _ & w).
      exact (X1 = [] /\ m0 = X3 /\ getchar_pre X3 w X2).
  - simpl; intros ??? ot ???.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (ot <> AST.Tvoid /\ putchar_post m0 X3 i w X2).
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (ot <> AST.Tvoid /\ getchar_post m0 X3 i w X2).
  - intros; exact True.
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
      destruct e; inv H; simpl in *.
      destruct vl; try contradiction; simpl in *.
      destruct H0, vl; try contradiction.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      assert (Harg: v = Vubyte c) by (inv Hargs; auto). clear Hargs.
      rewrite Harg.
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | apply join_comm, core_unit]; subst; auto.
    + unfold funspec2pre; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct t as (? & ? & k); simpl in *.
      destruct H2 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      destruct e; inv H0; simpl in *.
      destruct vl; try contradiction.
      unfold putchar_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      unfold getchar_pre.
      eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | apply join_comm, core_unit]; subst; auto.
  - unfold funspec2pre, funspec2post, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct H0 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & (c, k)); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (? & Hmem & ? & Hw); simpl in Hw; subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost x, NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      split; [|split3].
      * eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * exists i.
        split3; simpl.
        -- split; auto.
        -- unfold_lift. split; auto. split; [|intro Hx; inv Hx].
             unfold eval_id; simpl. unfold semax.make_ext_rval; simpl.
             destruct ot; try contradiction; reflexivity.
        -- unfold SEPx; simpl.
           rewrite seplog.sepcon_emp.
           unfold ITREE; exists x; split; [if_tac; auto|].
           { subst; apply eutt_sutt, Eq.Reflexive_eqit_eq. }
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
      destruct H0 as (_ & vl & z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & k); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (? & Hmem & ? & Hw); simpl in Hw; subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost x, NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      split; [|split3].
      * eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * exists i.
        split3; simpl.
        -- split; auto.
        -- unfold_lift. split; auto. split; [|intro Hx; inv Hx].
             unfold eval_id; simpl. unfold semax.make_ext_rval; simpl.
             destruct ot; try contradiction; reflexivity.
        -- unfold SEPx; simpl.
             rewrite seplog.sepcon_emp.
             unfold ITREE; exists x; split; [if_tac; auto|].
             { subst; apply eutt_sutt, Eq.Reflexive_eqit_eq. }
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
    destruct Hpost as (? & ? & ?); subst.
    reflexivity.
  - if_tac in Hpre; [|contradiction].
    destruct w as (m0 & _ & w).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost as (? & ? & ?); subst.
    reflexivity.
Qed.

End IO_Dry.
