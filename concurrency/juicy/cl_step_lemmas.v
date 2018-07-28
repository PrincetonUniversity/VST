Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory. Import Memory.
Require Import compcert.common.Memdata. Import Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.veric.Clight_new.
Require Import VST.veric.coqlib4.
Require Import VST.sepcomp.Address.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.common.permissions.

Set Bullet Behavior "Strict Subproofs".

(** * Results on cl_step *)

Lemma cl_step_decay ge c m c' m' : @cl_step ge c m c' m' -> @decay m m'.
Proof.
  intros step.
  induction step
    as [ ve te k m a1 a2 b ofs v2 v m' H H0 H1 H2 ASS | |
         ve te k m optid a al tyagrs tyres cc vf vargs f m'  ve' le' H H0 H1 H2 H3 H4 NRV ALLOC H6
         | | | | | | | | | f ve te optexp optid k m v' m' ve' te'' k' H H0 FREE H2 H3 | | | ];
    try apply decay_refl || apply IHstep.

  - (* assign: no change in permission *)
    intros b' ofs'.
    split.
    + inversion ASS as [v0 chunk m'0 H3 BAD H5 H6 | b'0 ofs'0 bytes m'0 H3 H4 H5 H6 H7 BAD H9 H10]; subst.
      -- pose proof storev_valid_block_2 _ _ _ _ _ BAD b'. tauto.
      -- pose proof Mem.storebytes_valid_block_2 _ _ _ _ _ BAD b'. tauto.
    + intros V; right; intros kind.
      (* destruct m as [c acc nb max no def]. simpl in *. *)
      inversion ASS as [v0 chunk m'0 H3 STO H5 H6 | b'0 ofs'0 bytes m'0 H3 H4 H5 H6 H7 STO H9 H10]; subst.
      -- simpl in *.
         Transparent Mem.store.
         unfold Mem.store in *; simpl in *.
         destruct (Mem.valid_access_dec m chunk b (Ptrofs.unsigned ofs) Writable).
         2:discriminate.
         injection STO as <-. simpl.
         reflexivity.
      -- Transparent Mem.storebytes.
         unfold Mem.storebytes in *.
         destruct (Mem.range_perm_dec
                     m b (Ptrofs.unsigned ofs)
                     (Ptrofs.unsigned ofs + Z.of_nat (Datatypes.length bytes)) Cur Writable).
         2:discriminate.
         injection STO as <-. simpl.
         reflexivity.

  - (* internal call : allocations *)
    clear -ALLOC.
    induction ALLOC. now apply decay_refl.
    apply decay_trans with m1. 3:apply IHALLOC.

    + clear -H.
      Transparent Mem.alloc.
      unfold Mem.alloc in *.
      injection H as <- <-.
      intros b V.
      unfold Mem.valid_block in *. simpl.
      apply Coqlib.Plt_trans_succ, V.

    + clear -H.
      unfold Mem.alloc in *.
      injection H as E <-.
      intros b ofs.
      split.
      * intros N V.
        subst m1.
        simpl in *.
        rewrite PMap.gsspec.
        unfold Mem.valid_block in *; simpl in *.
        if_tac; subst; auto.
        -- simple_if_tac; auto.
        -- destruct N.
           apply Coqlib.Plt_succ_inv in V.
           tauto.
      * intros V.
        right.
        intros k.
        subst.
        simpl.
        rewrite PMap.gsspec.
        if_tac.
        -- subst b. inversion V. rewrite Pos.compare_lt_iff in *. edestruct Pos.lt_irrefl; eauto.
        -- reflexivity.

  - (* return: free_list *)
    revert FREE; clear.
    generalize (blocks_of_env ge ve); intros l.
    revert m m'; induction l as [| [[b o] o'] l IHl]; intros m m'' E.
    + simpl. injection E as <- ; apply decay_refl.
    + simpl in E.
      destruct (Mem.free m b o o') as [m' |] eqn:F.
      2:discriminate.
      specialize (IHl _ _ E).
      Transparent Mem.free.
      unfold Mem.free in *.
      if_tac in F. rename H into G.
      2:discriminate.
      apply decay_trans with m'. 3:now apply IHl.
      * injection F as <-.
        intros.
        unfold Mem.unchecked_free, Mem.valid_block in *.
        simpl in *.
        assumption.

      * injection F as <-.
        clear -G.
        unfold Mem.unchecked_free in *.
        intros b' ofs; simpl. unfold Mem.valid_block; simpl.
        split.
        tauto.
        intros V.
        rewrite PMap.gsspec.
        if_tac; auto. subst b'.
        hnf in G.
        destruct (Coqlib.proj_sumbool (Coqlib.zle o ofs)&&Coqlib.proj_sumbool (Coqlib.zlt ofs o'))%bool eqn:E.
        2: now auto.
        left. split; auto.
        destruct m as [co acc nb max noa def] eqn:Em; simpl in *.
        unfold Mem.perm in G; simpl in *.
        specialize (G ofs).
        cut (acc !! b ofs Cur = Some Freeable). {
          destruct k; auto.
          pose proof Mem.access_max m b ofs as M.
          subst m; simpl in M.
          intros A; rewrite A in M.
          destruct (acc !! b ofs Max) as [ [] | ]; inversion M; auto.
        }
        assert (R: (o <= ofs < o')%Z). {
          rewrite andb_true_iff in *. destruct E as [E F].
          apply Coqlib.proj_sumbool_true in E.
          apply Coqlib.proj_sumbool_true in F.
          auto.
        }
        autospec G.
        destruct (acc !! b ofs Cur) as [ [] | ]; inversion G; auto.
Qed.

Lemma cl_step_unchanged_on ge c m c' m' b ofs :
  @cl_step ge c m c' m' ->
  Mem.valid_block m b ->
  ~ Mem.perm m b ofs Cur Writable ->
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
Proof.
  intros step.
  induction step
    as [ ve te k m a1 a2 b0 ofs0 v2 v m' H H0 H1 H2 ASS | |
         ve te k m optid a al tyagrs tyres cc vf vargs f m'  ve' le' H H0 H1 H2 H3 H4 NRV ALLOC H6
         | | | | | | | | | f ve te optexp optid k m v' m' ve' te'' k' H H0 FREE H2 H3 | | | ];
    intros V NW; auto.

  - (* assign: some things are updated, but not the chunk in non-writable permission *)
    inversion ASS; subst.
    + inversion H4.
      unfold Mem.store in *.
      destruct (Mem.valid_access_dec m chunk b0 (Ptrofs.unsigned ofs0) Writable); [|discriminate].
      injection H6 as <- ; clear ASS H4.
      simpl.
      destruct (eq_dec b b0) as [e|n]; swap 1 2.
      * rewrite PMap.gso; auto.
      * subst b0. rewrite PMap.gss.
        generalize ((Mem.mem_contents m) !! b); intros t.
        destruct v0 as [v0 align].
        specialize (v0 ofs).
        {
          destruct (adr_range_dec (b, Ptrofs.unsigned ofs0) (size_chunk chunk) (b, ofs)) as [a|a].
          - simpl in a; destruct a as [_ a].
            autospec v0.
            tauto.
          - simpl in a.
            symmetry.
            apply Mem.setN_outside.
            rewrite encode_val_length.
            replace (Z_of_nat (size_chunk_nat chunk)) with (size_chunk chunk); swap 1 2.
            { unfold size_chunk_nat in *. rewrite Z2Nat.id; auto. destruct chunk; simpl; omega. }
            assert (a' : ~ (Ptrofs.unsigned ofs0 <= ofs < Ptrofs.unsigned ofs0 + size_chunk chunk)%Z) by intuition.
            revert a'; clear.
            generalize (Ptrofs.unsigned ofs0).
            generalize (size_chunk chunk).
            intros.
            omega.
        }

    + (* still the case of assignment (copying) *)
      unfold Mem.storebytes in *.
      destruct (Mem.range_perm_dec m b0 (Ptrofs.unsigned ofs0) (Ptrofs.unsigned ofs0 + Z.of_nat (Datatypes.length bytes)) Cur Writable); [ | discriminate ].
      injection H8 as <-; clear ASS; simpl.
      destruct (eq_dec b b0) as [e|n]; swap 1 2.
      * rewrite PMap.gso; auto.
      * subst b0. rewrite PMap.gss.
        generalize ((Mem.mem_contents m) !! b); intros t.
        specialize (r ofs).
        {
          destruct (adr_range_dec (b, Ptrofs.unsigned ofs0) (Z.of_nat (Datatypes.length bytes)) (b, ofs)) as [a|a].
          - simpl in a; destruct a as [_ a].
            autospec r.
            tauto.
          - simpl in a.
            symmetry.
            apply Mem.setN_outside.
            assert (a' : ~ (Ptrofs.unsigned ofs0 <= ofs < Ptrofs.unsigned ofs0 + Z.of_nat (Datatypes.length bytes))%Z) by intuition.
            revert a'; clear.
            generalize (Ptrofs.unsigned ofs0).
            intros.
            omega.
        }

  - (* internal call : things are allocated -- each time in a new block *)
    clear -V ALLOC.
    induction ALLOC. easy.
    rewrite <-IHALLOC; swap 1 2.
    + unfold Mem.alloc in *.
      injection H as <- <-.
      unfold Mem.valid_block in *.
      simpl.
      apply Plt_trans_succ.
      auto.
    + clear IHALLOC.
      unfold Mem.alloc in *.
      injection H as <- <- . simpl.
      f_equal.
      rewrite PMap.gso. auto.
      unfold Mem.valid_block in *.
      auto with *.

  - (* return: free_list *)
    revert FREE NW V; clear.
    generalize (blocks_of_env ge ve); intros l.
    revert m m'; induction l as [| [[b' o] o'] l IHl]; intros m m'' E NW V.
    + simpl. injection E as <- . easy.
    + simpl in E.
      destruct (Mem.free m b' o o') as [m' |] eqn:F.
      2:discriminate.
      specialize (IHl _ _ E).
      unfold Mem.free in *.
      if_tac in F. 2:discriminate.
      injection F as <- .
      rewrite <-IHl. easy.
      * unfold Mem.perm in *.
        unfold Mem.unchecked_free.
        simpl.
        rewrite PMap.gsspec.
        if_tac; [ | easy ].
        subst.
        unfold Mem.range_perm in *.
        destruct (zle o ofs); auto.
        destruct (zlt ofs o'); simpl; auto.
      * unfold Mem.unchecked_free, Mem.valid_block; simpl. auto.
Qed.
