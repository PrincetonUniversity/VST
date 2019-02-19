Require Import VST.progs.io_specs_mem.
Require Import VST.progs.io_mem.
Require Import VST.floyd.proofauto.
Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Eq.Utt.
Import MonadNotations.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.veric.SequentialClight.
Require Import VST.progs.conclib.
Require Import VST.progs.dry_mem_lemmas.
Require Import VST.veric.mem_lessdef.

Definition getchars_pre (m : mem) (witness : share * val * Z * (list int -> IO_itree)) (z : IO_itree) :=
  let '(sh, buf, len, k) := witness in (z = (r <- read_list (Z.to_nat len);; k r))%eq_utt /\
    match buf with Vptr b ofs =>
      Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + Z.max 0 len) Memtype.Cur Memtype.Writable
      | _ => False end.

Definition getchars_post (m0 m : mem) r (witness : share * val * Z * (list int -> IO_itree)) (z : IO_itree) :=
  let '(sh, buf, len, k) := witness in r = Int.repr len /\ exists msg, z = k msg /\
    match buf with Vptr b ofs => exists m', store_byte_list m0 b (Ptrofs.unsigned ofs) (map Vint msg) = Some m' /\
        mem_equiv m m'
    | _ => False end.

Definition putchars_pre (m : mem) (witness : share * val * list int * IO_itree) (z : IO_itree) :=
  let '(sh, buf, msg, k) := witness in (z = (write_list msg;; k))%eq_utt /\
  exists m0, match buf with Vptr b ofs =>
    store_byte_list m0 b (Ptrofs.unsigned ofs) (map Vint msg) = Some m
    | _ => False end.

Definition putchars_post (m0 m : mem) r (witness : share * val * list int * IO_itree) (z : IO_itree) :=
  let '(sh, buf, msg, k) := witness in m0 = m /\ r = Int.repr (Zlength msg) /\ z = k.

Program Definition io_dry_spec : external_specification mem external_function IO_itree.
Proof.
  unshelve econstructor.
  - intro e.
    pose (ext_spec_type IO_ext_spec e) as T; simpl in T.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|exact False]];
      match goal with T := (_ * ?A)%type |- _ => exact (mem * A)%type end.
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ getchars_pre X3 w X2).
    + destruct X as (m0 & _ & w).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ putchars_pre X3 w X2).
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (getchars_post m0 X3 i w X2).
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (putchars_post m0 X3 i w X2).
  - intros; exact False.
Defined.

Definition dessicate : forall ef (jm : juicy_mem), ext_spec_type IO_ext_spec ef -> ext_spec_type io_dry_spec ef.
Proof.
  simpl; intros.
  destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|assumption]].
  - destruct X as [_ X]; exact (m_dry jm, X).
  - destruct X as [_ X]; exact (m_dry jm, X).
Defined.

Theorem juicy_dry_specs : juicy_dry_ext_spec _ IO_ext_spec io_dry_spec dessicate.
Proof.
  split; [|split]; try reflexivity; simpl.
  - unfold funspec2pre, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct t as (? & ? & (((sh, buf), len), k)); simpl in *.
      destruct H1 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold getchars_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as ([Hwritable _] & _ & ? & ? & J1 & (? & ? & Htrace) & Hbuf).
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      split.
      * symmetry.
        eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | eauto]; subst; auto.
      * destruct (data_at__writable_perm _ _ _ _ jm Hwritable Hbuf) as (? & ? & ? & Hperm); subst; simpl.
        { eapply sepalg.join_sub_trans; [|eexists; eauto].
          eexists; eauto. }
        simpl in Hperm.
        rewrite Z.mul_1_l in Hperm; auto.
    + unfold funspec2pre; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct t as (? & ? & (((sh, buf), msg), k)); simpl in *.
      destruct H2 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold putchars_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as ([Hreadable _] & _ & ? & ? & J1 & (? & ? & Htrace) & Hbuf).
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      split.
      * symmetry.
        eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | eauto]; subst; auto.
      * (* data_at to bytes in mem *) admit.
  - unfold funspec2pre, funspec2post, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct H0 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & (((sh, buf), len), k)); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as ([Hwritable _] & _ & phig & phir & J1 & (? & ? & Htrace) & Hbuf).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (? & msg & ? & Hpost); subst.

      (* need to make the new rmap with the data in it *)
      admit.

(*
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost (k msg), NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      destruct buf; try contradiction.
      assert (readable_share sh) as Hreadable by auto.
      edestruct (data_at__VALspec_range _ _ _ _ Hreadable _ Hbuf) as [_ Hg]; auto.
      destruct (join_level _ _ _ J).
      split; [|split3].
      * apply ghost_of_join, join_comm, Hg in J1.
        rewrite J1 in Hgx.
        eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * exists msg.
        split3; simpl.
        { split; auto. }
        { split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate. }
        unfold SEPx; simpl.
        rewrite seplog.sepcon_emp.
        unshelve eexists (age_to.age_to _ (set_ghost phig _ _)), (age_to.age_to _ phir');
          try (split; [apply age_to.age_to_join_eq|]); try apply set_ghost_join; eauto.
        { unfold set_ghost; rewrite level_make_rmap; omega. }
        split.
        -- unfold ITREE; exists (k msg); split; [apply Reflexive_eq_utt|].
             eapply age_to.age_to_pred, change_has_ext; eauto.
        -- 
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H3; eexists; constructor; constructor.
        instantiate (1 := (_, _)).
        constructor; simpl; [|constructor; auto].
        apply ext_ref_join. *)
    + unfold funspec2pre, funspec2post, dessicate; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct H1 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & (((sh, buf), msg), k)); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as ([Hreadable _] & _ & phig & phir & J1 & (? & ? & Htrace) & Hbuf).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H5 as (Hmem & ? & ?); subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H3.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 [Some (ext_ghost k, NoneP)] _)), (age_to.age_to (level jm) phi1'); auto.
      destruct buf; try solve [destruct Hbuf as [[]]; contradiction].
      assert (res_predicates.noghost phir) as Hg.
      { eapply data_at__VALspec_range; eauto.
        apply data_at_data_at_ in Hbuf; eauto. }
      destruct (join_level _ _ _ J).
      split; [|split3].
      * apply ghost_of_join, join_comm, Hg in J1.
        rewrite J1 in Hgx.
        eapply age_rejoin; eauto.
        intro; rewrite H3; auto.
      * split3; simpl.
        { split; auto. }
        { split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate. }
        unfold SEPx; simpl.
        rewrite seplog.sepcon_emp.
        unshelve eexists (age_to.age_to _ (set_ghost phig _ _)), (age_to.age_to _ phir);
          try (split; [apply age_to.age_to_join_eq|]); try apply set_ghost_join; eauto.
        { unfold set_ghost; rewrite level_make_rmap; omega. }
        split.
        -- unfold ITREE; exists k; split; [apply Reflexive_eq_utt|].
             eapply age_to.age_to_pred, change_has_ext; eauto.
        -- apply age_to.age_to_pred; auto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H4; eexists; constructor; constructor.
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
  - destruct w as (m0 & _ & (((?, ?), ?), ?)).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost; subst.
    admit.
  - if_tac in Hpre; [|contradiction].
    destruct w as (m0 & _ & (((?, ?), ?), ?)).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost; subst.
    reflexivity.
Qed.

(* specialize whole_program_sequential_safety 
   Given that, what can we prove in CertiKOS about its execution? *)