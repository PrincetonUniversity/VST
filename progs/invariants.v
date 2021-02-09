Require Export VST.veric.invariants.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.conclib.
Require Export VST.progs.ghostsI.
Require Import VST.veric.bi.
Require Import VST.msl.sepalg.
Require Import List.

Definition cored : mpred := own.cored.

Lemma cored_dup : forall P, P && cored |-- (P && cored) * (P && cored).
Proof.
  constructor; apply own.cored_dup.
Qed.

Lemma cored_dup_cored : forall P, P && cored |-- ((P && cored) * (P && cored)) && cored.
Proof.
  constructor; apply cored_dup_cored.
Qed.

Lemma cored_duplicable : cored = cored * cored.
Proof.
  apply own.cored_duplicable.
Qed.

Lemma own_cored: forall {RA: Ghost} g a pp, join a a a -> own g a pp |-- cored.
Proof.
  intros; constructor; apply own.own_cored; auto.
Qed.

Lemma cored_sepcon: forall P Q, (P && cored) * (Q && cored) |-- (P * Q) && cored.
Proof.
  constructor; apply cored_sepcon.
Qed.

Lemma cored_dup_gen : forall P, (P |-- cored) -> P |-- P * P.
Proof.
  unseal_derives; exact cored_dup_gen.
Qed.

Lemma cored_emp: (cored |-- |==> emp)%I.
Proof.
  constructor; apply own.cored_emp.
Qed.

Lemma emp_cored : (emp |-- cored)%I.
Proof.
  constructor; apply own.emp_cored.
Qed.

Lemma iter_sepcon_eq : forall A, @invariants.iter_sepcon A = @iter_sepcon mpred A _ _.
Proof.
  intros; extensionality f; extensionality l.
  induction l; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma nth_replace_nth : forall {A} n l a (d : A), (n < length l)%nat ->
  nth n (replace_nth n l a) d = a.
Proof.
  induction n; destruct l; auto; simpl; intros; try omega.
  apply IHn; omega.
Qed.

Lemma nth_replace_nth' : forall {A} n m l a (d : A), m <> n ->
  nth m (replace_nth n l a) d = nth m l d.
Proof.
  induction n; destruct l; auto; destruct m; auto; simpl; intros; try omega.
  apply IHn; omega.
Qed.

Section Invariants.

Context {inv_names : invG}.

Lemma invariant_dup : forall i P, invariant i P = invariant i P * invariant i P.
Proof.
  exact invariant_dup.
Qed.

Lemma invariant_cored : forall i P, invariant i P |-- cored.
Proof.
  constructor; apply invariant_cored.
Qed.

Lemma wsat_alloc : forall P, wsat * |> P |-- (|==> wsat * EX i : _, invariant i P)%I.
Proof.
  intros; iIntros "[wsat P]".
  unfold wsat.
  iDestruct "wsat" as (l lg lb) "((((% & inv) & dis) & en) & I)".
  iMod (own_alloc(RA := unit_PCM) tt (pred_of P) with "[$]") as (g) "agree"; first (simpl; auto).
  replace (own(RA := unit_PCM) g () (pred_of P)) with (agree g P) by reflexivity.
  rewrite agree_dup.
  iDestruct "agree" as "[agree1 agree2]".
  iMod (own_update_ND(RA := list_PCM token_PCM) _ _ (fun l => exists i, l =
      map (fun o => match o with Some true => Some (Some tt) | _ => None end)
          ((lb ++ repeat None i) ++ [Some true])) with "dis") as (disb) "[% dis]".
  { intros ? (? & ? & _).
    exists (map (fun o => match o with Some true => Some (Some tt) | _ => None end)
      ((lb ++ repeat None (length x - length lb)) ++ [Some true])).
    split; [eauto|].
    exists (x ++ [Some (Some tt)]); split; simpl; auto.
    erewrite !map_app, own.map_repeat; simpl.
    pose proof (list_join_length _ _ _ H0) as Hlen.
    rewrite map_length in Hlen.
    apply join_comm in H0.
    pose proof (list_join_length _ _ _ H0) as Hlen'.
    apply (join_comm(Perm_alg := list_Perm)), (list_join_over c).
    { erewrite app_length, map_length, repeat_length, le_plus_minus_r; auto. }
    apply (join_comm(Perm_alg := list_Perm)), (list_join_filler(P := token_PCM));
      [|rewrite map_length; auto].
    apply join_comm in H0; auto. }
  destruct H0 as [i ?]; subst.
  destruct H.
  assert (Zlength lg = Zlength l) as Hlg by (apply Zlength_eq; auto).
  assert (Zlength lb = Zlength l) as Hlb by (apply Zlength_eq; auto).
  iMod (master_update(ORD := list_order _) _
        (map (fun j => match Znth j ((lb ++ repeat None i) ++ [Some true]) with
                       | Some _ => Some (Znth j ((lg ++ repeat O i) ++ [g]))
                       | None => None
                       end) (upto (length ((l ++ repeat emp i) ++ [P])))) with "inv") as "inv".
  { rewrite <- !app_assoc, app_length, upto_app, map_app.
    split.
    { erewrite app_length, !map_length; lia. }
    intros ?? Hn.
    erewrite app_nth, map_length.
    if_tac; [|erewrite nth_overflow in Hn by (rewrite map_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in * by auto.
    erewrite upto_length in *.
    assert (Z.of_nat n < Zlength l).
    { rewrite Zlength_correct; apply Nat2Z.inj_lt; auto. }
    erewrite nth_upto in * by auto.
    erewrite !app_Znth1 by lia; auto. }
  iMod (make_snap(ORD := list_order _) with "inv") as "[snap inv]".
  iMod (ghost_snap_forget(ORD := list_order _) (list_singleton (length lg + i) g) with "snap") as "snap".
  { apply list_incl_singleton.
    erewrite app_length, upto_app, map_app, app_nth2; erewrite map_length, upto_length, app_length,
      repeat_length; try lia.
    replace (_ - _)%nat with O by lia; simpl.
    rewrite Nat2Z.inj_add Z.add_0_r.
    rewrite !app_Znth2; erewrite !Zlength_app, !Zlength_repeat, <- Zlength_correct; try lia.
    replace (_ - _) with 0 by lia; replace (_ - _) with 0 by lia; auto. }
  iModIntro; iSplitR "agree2 snap".
  - iExists ((l ++ repeat emp i) ++ [P]), ((lg ++ repeat O i) ++ [g]),
         ((lb ++ repeat None i) ++ [Some true]).
    erewrite !(app_length (_ ++ _)); simpl.
    erewrite !iter_sepcon_eq, upto_app, iter_sepcon_app; simpl.
    erewrite Z.add_0_r, <- Zlength_correct, !app_Znth2; erewrite !Zlength_app, !Zlength_repeat; try lia.
    erewrite Hlg, Hlb, Zminus_diag, !Znth_0_cons.
    erewrite predicates_hered.prop_true_andp by (erewrite !app_length, !repeat_length; lia).
    iFrame.
    iSplitL "en".
    + erewrite Ensembles.Extensionality_Ensembles at 1; [iApply "en"|].
      constructor; intros ? X; unfold Ensembles.In in *.
      * destruct (lt_dec x (length lb)).
      rewrite !app_nth app_length.
      destruct (lt_dec _ _); [|omega].
      destruct (lt_dec _ _); [auto | omega].
      { rewrite -> nth_overflow in X by omega; discriminate. }
      * rewrite !app_nth nth_repeat in X.
      repeat destruct (lt_dec _ _); auto; try discriminate.
      destruct (x - _)%nat; [|destruct n0]; inv X.
    + erewrite app_length, upto_app, iter_sepcon_app.
      rewrite <- sepcon_emp at 1; iDestruct "I" as "[I emp]".
      iSplitL "I".
      * erewrite iter_sepcon_func_strong; [iApply "I"|].
        intros ??%In_upto.
        rewrite <- Zlength_correct in *.
        rewrite <- !app_assoc, !app_Znth1 by (rewrite ?Zlength_app; lia); auto.
      * rewrite iter_sepcon_emp'; auto.
        intros ? Hin.
        eapply in_map_iff in Hin as (? & ? & Hin%In_upto); subst.
        rewrite <- Zlength_correct, Zlength_repeat in Hin.
        rewrite <- Zlength_correct, <- app_assoc, app_Znth2 by lia.
        erewrite app_Znth1, Znth_repeat'; auto; try lia.
        rewrite Zlength_repeat; lia.
  - iExists (length l + i)%nat; unfold invariant.
    iExists g; rewrite H; iFrame.
Qed.

Lemma agree_join : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P1.
Proof.
  constructor; apply agree_join.
Qed.

Lemma agree_join2 : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P2.
Proof.
  constructor; apply agree_join2.
Qed.

Existing Instance token_PCM.

Lemma wsat_open : forall i P,
  (wsat * invariant i P * ghost_set g_en (Ensembles.Singleton i) |--
  |==> wsat * |> P * ghost_list g_dis (list_singleton i (Some tt)))%I.
Proof.
  intros; unfold wsat, invariant.
  iIntros "((H & inv1) & en1)". iDestruct "H" as (l lg lb) "((((% & inv) & dis) & en) & I)". iDestruct "inv1" as (g) "[snap agree]".
  iAssert (!! (i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat) as %Hi.
  { iCombine "snap" "inv" as "inv"; unfold master_list; erewrite snap_master_join1.
    iDestruct "inv" as "[% inv]".
    apply list_incl_singleton in H0.
    destruct (lt_dec i (length lg));
      [|erewrite nth_overflow in H0 by (erewrite map_length, upto_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in H0 by (rewrite upto_length; lia).
    erewrite nth_upto in H0 by lia.
    destruct (Znth (Z.of_nat i) lb); inv H0; iPureIntro; eauto. }
  iMod (@own_dealloc (snap_PCM(ORD := list_order _)) with "snap").
  iModIntro.
  destruct Hi as (? & ? & b & Hi).
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth' in Hi; auto).
  destruct b.
  erewrite ghost_list_nth with (n := i) by (erewrite nth_map' with (d' := None), Hi'; eauto; lia).
  iDestruct "dis" as "[token dis]".
  rewrite -> iter_sepcon_eq, iter_sepcon_Znth with (i0 := Z.of_nat i)
    by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
  erewrite Znth_upto, Hi by lia.
  iDestruct "I" as "((agree' & HP) & I)".
  subst; iDestruct (agree_join with "[agree agree']") as "[imp agree]"; first iFrame.
  iSplitR "token"; last iFrame.
  iSplitR "HP imp"; last (iApply "imp"; iFrame).
  iExists l, lg, (replace_nth i lb (Some false)).
  rewrite replace_nth_length predicates_hered.prop_true_andp; last auto.
  iSplitR "I agree".
  iSplitR "en en1".
  iSplitR "dis".
  - erewrite map_ext; [iFrame|].
    intros; simpl.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto.
  - rewrite map_replace_nth; iFrame.
  - iCombine "en en1" as "en"; erewrite ghost_set_join.
    iDestruct "en" as "[% en]".
    erewrite Ensembles.Extensionality_Ensembles at 1; [iFrame | constructor; intros ? X].
    + destruct (eq_dec x i).
      * subst; unfold Ensembles.In; apply nth_replace_nth; omega.
      * inv X; unfold Ensembles.In in *.
        rewrite nth_replace_nth'; auto.
        { inv H2; contradiction. }
    + destruct (eq_dec x i); [subst; right; constructor | left].
      unfold Ensembles.In in *.
      rewrite nth_replace_nth' in X; auto.
  - erewrite iter_sepcon_Znth with (i0 := Z.of_nat i)(l0 := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite Znth_upto, Znth_replace_nth by lia; iFrame.
    erewrite iter_sepcon_func_strong; auto.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia.
  - iCombine "en en1" as "en"; erewrite ghost_set_join.
    iDestruct "en" as "[% en]".
    inv H2.
    contradiction (H3 i); constructor; auto; constructor.
Qed.

(* up *)
Lemma replace_nth_same' : forall {A} n l (a d : A), nth n l d = a -> replace_nth n l a = l.
Proof.
  intros; subst; apply replace_nth_same.
Qed.

Lemma wsat_close : forall i P,
  (wsat * invariant i P * |> P * ghost_list g_dis (list_singleton i (Some tt)) |--
  |==> wsat * ghost_set g_en (Ensembles.Singleton i))%I.
Proof.
  intros; unfold wsat, invariant.
  iIntros "(((H & inv1) & HP) & dis1)". iDestruct "H" as (l lg lb) "((((% & inv) & dis) & en) & I)". iDestruct "inv1" as (g) "[snap agree]".
  iAssert (!!(i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat) as %Hi.
  { iCombine "snap inv" as "inv"; unfold master_list; erewrite snap_master_join1.
    iDestruct "inv" as "[% inv]".
    apply list_incl_singleton in H0.
    destruct (lt_dec i (length lg));
      [|erewrite nth_overflow in H0 by (erewrite map_length, upto_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in H0 by (rewrite upto_length; lia).
    erewrite nth_upto in H0 by lia.
    destruct (Znth (Z.of_nat i) lb); inv H0; eauto. }
  iMod (@own_dealloc (snap_PCM(ORD := list_order _)) with "snap").
  iModIntro.
  destruct Hi as (? & ? & b & Hi).
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth' in Hi; auto).
  destruct b.
  { iCombine "dis dis1" as "dis".
    iDestruct (own_valid_2(RA := list_PCM _) with "[$dis]") as %H2.
    destruct H2 as (? & J & _).
    apply list_join_nth with (n := i) in J.
    erewrite nth_singleton, nth_map' with (d' := None) in J by lia.
    rewrite Hi' in J; inv J.
    inv H5.
    inv H3. }
  erewrite ghost_set_remove with (a := i).
  iDestruct "en" as "[$ en]".
  iExists l, lg, (replace_nth i lb (Some true)).
  rewrite replace_nth_length predicates_hered.prop_true_andp; last auto.
  iSplitR "I agree HP".
  iSplitR "en".
  iSplitR "dis dis1".
  - erewrite map_ext; [iFrame|].
    intros.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto.
  - iCombine "dis1 dis" as "dis"; setoid_rewrite <- own.ghost_op; [iFrame|].
    rewrite map_replace_nth.
    apply (list_join_singleton(P := token_PCM)).
    { rewrite map_length; lia. }
    erewrite nth_map' with (d' := None) by lia.
    rewrite Hi'; constructor.
  - erewrite Ensembles.Extensionality_Ensembles at 1; [iFrame|]; constructor; intros ? X.
    + inv X; unfold Ensembles.In in *.
      rewrite nth_replace_nth'; auto.
      intro; subst; contradiction.
    + constructor.
      * unfold Ensembles.In in *.
        destruct (eq_dec x i); [subst; auto|].
        rewrite nth_replace_nth' in X; auto.
      * intro X'; inv X'.
        unfold Ensembles.In in X.
        rewrite -> nth_replace_nth in X by omega; inv X.
  - erewrite !iter_sepcon_eq, iter_sepcon_Znth with (i0 := Z.of_nat i)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite iter_sepcon_Znth with (i0 := Z.of_nat i)(l0 := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite !Znth_upto, !Znth_replace_nth by lia.
    rewrite Hi.
    iDestruct "I" as "[agree' I]".
    subst; iDestruct (agree_join2 with "[agree' agree]") as "[imp agree]"; first by iFrame.
    iPoseProof ("imp" with "HP") as "?"; iFrame.
    erewrite iter_sepcon_func_strong; eauto.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia.
  - unfold Ensembles.In; auto.
Qed.

Lemma invariant_dealloc : forall i P, invariant i P |-- |==> emp.
Proof.
  constructor; apply invariant_dealloc.
Qed.

(* Consider putting rules for invariants and fancy updates in msl (a la ghost_seplog), and proofs
   in veric (a la own). *)

End Invariants.

Lemma make_wsat : emp |-- |==> EX inv_names : invG, wsat.
Proof.
  unfold wsat.
  iIntros.
  iMod (own_alloc(RA := snap_PCM(ORD := list_order gname)) (Tsh, nil) NoneP with "[$]") as (g_inv) "inv"; first (simpl; auto).
  iMod (own_alloc(RA := list_PCM (exclusive_PCM unit)) nil NoneP with "[$]") as (g_dis) "dis"; first (simpl; auto).
  iMod (own_alloc(RA := set_PCM) empty NoneP with "[$]") as (g_en) "en"; first (simpl; auto).
  iModIntro.
  iExists {| g_inv := g_inv; g_dis := g_dis; g_en := g_en |}.
  iExists nil, nil, nil; simpl; iFrame "inv dis en"; auto.
Qed.
