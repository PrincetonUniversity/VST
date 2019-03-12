Require Import ITree.ITree.
Require Import VST.progs.io_mem_specs.
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
Require Import VST.veric.mem_lessdef.
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

Definition ints_to_memvals li := concat (map (fun i => encode_val Mint8unsigned (Vint i)) li).

Lemma ints_to_memvals_length : forall li, Zlength (ints_to_memvals li) = Zlength li.
Proof.
  intros.
  rewrite !Zlength_correct; f_equal.
  unfold ints_to_memvals.
  rewrite <- map_map, encode_vals_length, map_length; auto.
Qed.

Definition getchars_pre (m : mem) (witness : share * val * Z * (list int -> IO_itree)) (z : IO_itree) :=
  let '(sh, buf, len, k) := witness in (eutt eq z (r <- read_list (Z.to_nat len);; k r)) /\
    match buf with Vptr b ofs =>
      Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + Z.max 0 len) Memtype.Cur Memtype.Writable
      | _ => False end.

Definition getchars_post (m0 m : mem) r (witness : share * val * Z * (list int -> IO_itree)) (z : IO_itree) :=
  let '(sh, buf, len, k) := witness in r = Int.repr len /\
    exists msg, Zlength msg = len /\ Forall (fun i => Int.unsigned i <= Byte.max_unsigned) msg /\ z = k msg /\
    match buf with Vptr b ofs => exists m', Mem.storebytes m0 b (Ptrofs.unsigned ofs) (ints_to_memvals msg) = Some m' /\
        mem_equiv m m'
    | _ => False end.

Definition putchars_pre (m : mem) (witness : share * val * list int * Z * list val * IO_itree) (z : IO_itree) :=
  let '(sh, buf, msg, _, _, k) := witness in (eutt eq z (write_list msg;; k)) /\
  match buf with Vptr b ofs =>
    Mem.loadbytes m b (Ptrofs.unsigned ofs) (Zlength msg) =
      Some (ints_to_memvals msg)
    | _ => False end.

Definition putchars_post (m0 m : mem) r (witness : share * val * list int * Z * list val * IO_itree) (z : IO_itree) :=
  let '(sh, buf, msg, _, _, k) := witness in m0 = m /\ r = Int.repr (Zlength msg) /\ z = k.

Context {CS : compspecs} (ext_link : String.string -> ident).

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
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ putchars_pre X3 w X2).
    + destruct X as (m0 & _ & w).
      exact (Val.has_type_list X1 (sig_args (ef_sig e)) /\ m0 = X3 /\ getchars_pre X3 w X2).
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (putchars_post m0 X3 i w X2).
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (getchars_post m0 X3 i w X2).
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
      destruct t as (? & ? & (((((sh, buf), msg), len), rest), k)); simpl in *.
      destruct H1 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      unfold putchars_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as ([Hreadable _] & _ & ? & ? & J1 & (? & ? & Htrace) & Hbuf).
      apply has_ext_eq in Htrace.
      eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
      split.
      * symmetry.
        eapply has_ext_join in Hext as []; [| rewrite Htrace; reflexivity | eauto]; subst; auto.
      * assert (Z.max 0 len = Zlength msg + Zlength rest) as Hlen.
        { apply data_array_at_local_facts in Hbuf as (_ & ? & _).
          rewrite Zlength_app, Zlength_map in *; auto. }
        destruct (zlt len 0).
        { rewrite Z.max_l in Hlen by omega.
          destruct msg; [|rewrite Zlength_cons in *; rep_omega].
          destruct Hbuf as [[? _]]; destruct buf; try contradiction.
          rewrite Zlength_nil; apply Mem.loadbytes_empty; auto; omega. }
        rewrite Z.max_r in Hlen by omega; subst.
        rewrite split2_data_at_Tarray_app with (mid := Zlength msg) in Hbuf.
        destruct Hbuf as (? & ? & ? & Hbuf & _).
        eapply data_at_bytes in Hbuf; eauto.
        rewrite map_map in Hbuf; eauto.
        { rewrite Zlength_map; auto. }
        { eapply join_sub_trans; [|eexists; eauto].
          eapply join_sub_trans; eexists; eauto. }
        { apply Forall_map, Forall_forall; simpl; discriminate. }
        { rewrite Zlength_map; auto. }
        { rewrite Z.add_simpl_l; auto. }
    + clear H.
      unfold funspec2pre; simpl.
      if_tac; [|contradiction].
      intros; subst.
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
  - unfold funspec2pre, funspec2post, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct H0 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & (((((sh, buf), msg), len), rest), k)); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as ([Hwritable _] & _ & phig & phir & J1 & (? & ? & Htrace) & Hbuf).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (Hmem & ? & ?); subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
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
        intro; rewrite H2; auto.
      * split3; simpl.
        { split; auto. }
        { split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate. }
        unfold SEPx; simpl.
        rewrite seplog.sepcon_emp.
        unshelve eexists (age_to.age_to _ (set_ghost phig _ _)), (age_to.age_to _ phir);
          try (split; [apply age_to.age_to_join_eq|]); try apply set_ghost_join; eauto.
        { unfold set_ghost; rewrite level_make_rmap; omega. }
        split.
        -- unfold ITREE; exists k; split; [apply Reflexive_eutt|].
             eapply age_to.age_to_pred, change_has_ext; eauto.
        -- apply age_to.age_to_pred; auto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H3; eexists; constructor; constructor.
        instantiate (1 := (_, _)).
        constructor; simpl; [|constructor; auto].
        apply ext_ref_join.
    + clear H.
      unfold funspec2pre, funspec2post, dessicate; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct H0 as (_ & vl& z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & (((sh, buf), len), k)); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as ([Hwritable _] & _ & phig & phir & J1 & (? & ? & Htrace) & Hbuf).
      pose proof (has_ext_eq _ _ Htrace) as Hgx.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (? & msg & ? & Hbounds & ? & Hpost); subst.
      destruct buf; try contradiction.
      destruct Hpost as (m' & Hstore & Heq).
      exists (set_ghost (age_to.age_to (level jm) (inflate_store m' phi0)) [Some (ext_ghost (k msg), NoneP)] eq_refl),
        (age_to.age_to (level jm) phi1').
      destruct (join_level _ _ _ J).
      assert (Ptrofs.unsigned i + Zlength msg <= Ptrofs.max_unsigned) as Hbound.
      { destruct Hbuf as [(_ & _ & Hsize & _) _]; simpl in Hsize.
        rewrite Z.max_r in Hsize; rep_omega. }
      apply data_at__VALspec_range in Hbuf; auto.
      split.
      * apply resource_at_join2.
        -- unfold set_ghost; rewrite level_make_rmap.
           rewrite age_to.level_age_to; auto.
           unfold inflate_store; rewrite level_make_rmap.
           rewrite level_juice_level_phi; omega.
        -- rewrite age_to.level_age_to; auto.
           rewrite level_juice_level_phi; omega.
        -- intros.
           unfold set_ghost; rewrite resource_at_make_rmap.
           eapply rebuild_store; eauto.
           intros (b', o') ???? Hr1 []; subst.
           apply (resource_at_join _ _ _ (b', o')) in J; rewrite Hr1 in J.
           apply VALspec_range_e with (loc := (b', o')) in Hbuf as [? Hr].
           apply (resource_at_join _ _ _ (b', o')) in J1; rewrite Hr in J1.
           inv J1; rewrite <- H14 in J; inv J; eapply join_writable_readable; eauto;
             apply join_comm in RJ; eapply join_writable1; eauto.
           { rewrite ints_to_memvals_length in *; split; auto. }
        -- unfold set_ghost; rewrite ghost_of_make_rmap, !age_to_resource_at.age_to_ghost_of.
           rewrite H3.
           destruct Hbuf as [_ Hg].
           apply ghost_of_join, join_comm, Hg in J1; rewrite J1 in Hgx.
           apply ghost_of_join in J; rewrite Hgx in J.
           eapply change_ext in J; eauto.
           apply ghost_fmap_join with (f := approx (level jm))(g := approx (level jm)) in J.
           apply J.
      * split3.
        -- exists msg.
           split3; simpl.
           { split; auto. }
           { split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate. }
           unfold SEPx; simpl.
           rewrite seplog.sepcon_emp.
           unshelve eexists (set_ghost (age_to.age_to _ phig) _ _), (age_to.age_to _ (inflate_store m' phir));
             try (split3; [apply set_ghost_join; [apply age_to.age_to_join_eq|] | ..]).
           ++ reflexivity.
           ++ eapply inflate_store_join1, has_ext_noat; eauto.
           ++ unfold inflate_store; rewrite level_make_rmap; omega.
           ++ apply age_to.age_to_pred; simpl.
              unfold inflate_store; rewrite ghost_of_make_rmap.
              apply Hbuf.
           ++ unfold ITREE; exists (k msg); split; [apply Reflexive_eutt|].
              eapply change_has_ext, age_to.age_to_pred; eauto.
           ++ apply age_to.age_to_pred.
              rewrite <- (Zlength_map _ _ Vint).
              eapply store_bytes_data_at; rewrite ?Zlength_map; auto.
              { rewrite Forall_map; eapply Forall_impl, Hbounds; eauto. }
              { rewrite map_map; eauto. }
        -- eapply necR_trans; eauto; apply age_to.age_to_necR.
        -- rewrite H3; eexists; constructor; constructor.
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
  - destruct w as (m0 & _ & (((((?, ?), ?), ?), ?), ?)).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost; subst.
    reflexivity.
  - if_tac in Hpre; [|contradiction].
    destruct w as (m0 & _ & (((?, ?), ?), ?)).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost as (? & msg & ? & ? & ? & Hpost); subst.
    destruct v0; try contradiction.
    destruct Hpost as (? & Hstore & ?).
    eapply mem_evolve_equiv2; [|apply mem_equiv_sym; eauto].
    eapply mem_evolve_access, storebytes_access; eauto.
Qed.

End IO_Dry.
