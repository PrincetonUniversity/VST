From stdpp Require Export namespaces coPset.
From VST.veric Require Import compcert_rmaps fupd.
From VST.msl Require Import ghost ghost_seplog sepalg_generators.
From VST.concurrency Require Import ghosts conclib invariants cancelable_invariants.
Require Export VST.veric.bi.
Import FashNotation.

Lemma timeless'_timeless : forall (P : mpred), timeless' P -> Timeless P.
Proof.
  intros; unfold Timeless.
  constructor.
  apply timeless'_except_0; auto.
Qed.

#[export] Instance own_timeless : forall {P : Ghost} g (a : G), Timeless (own g a NoneP).
Proof.
  intros; apply timeless'_timeless, own_timeless.
Qed.

Lemma address_mapsto_timeless : forall m v sh p, Timeless (res_predicates.address_mapsto m v sh p : mpred).
Proof.
  intros; apply timeless'_timeless, address_mapsto_timeless.
Qed.

#[export] Instance timeless_FF : Timeless FF.
Proof.
  unfold Timeless; intros.
  iIntros ">?"; auto.
Qed.

Lemma nonlock_permission_bytes_timeless : forall sh l z,
  Timeless (res_predicates.nonlock_permission_bytes sh l z : mpred).
Proof.
  intros; apply timeless'_timeless, nonlock_permission_bytes_timeless.
Qed.

Lemma mapsto_timeless : forall sh t v p, Timeless (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try apply timeless_FF.
  destruct (type_is_volatile); try apply timeless_FF.
  destruct p; try apply timeless_FF.
  if_tac.
  - apply (@bi.or_timeless mpredI).
    + apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply address_mapsto_timeless].
    + apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI)|].
      apply (@bi.exist_timeless mpredI); intro; apply address_mapsto_timeless.
  - apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply nonlock_permission_bytes_timeless].
Qed.

#[export] Instance emp_timeless : (@Timeless mpredI) emp.
Proof.
  apply timeless'_timeless, emp_timeless.
Qed.

Lemma memory_block'_timeless : forall sh n b z,
  Timeless (mapsto_memory_block.memory_block' sh n b z).
Proof.
  induction n; simpl; intros.
  - apply emp_timeless.
  - apply (@bi.sep_timeless), IHn.
    apply mapsto_timeless.
Qed.

Lemma memory_block_timeless : forall sh n p,
  Timeless (memory_block sh n p).
Proof.
  intros.
  destruct p; try apply timeless_FF.
  apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply memory_block'_timeless].
Qed.

Lemma struct_pred_timeless : forall {CS : compspecs} sh m f t off
  (IH : Forall (fun it : _ =>
        forall (v : reptype (t it)) (p : val),
        Timeless (data_at_rec sh (t it) v p)) m) v p,
  Timeless (struct_pred m (fun (it : _) v =>
      withspacer sh (f it + sizeof (t it)) (off it)
        (at_offset (data_at_rec sh (t it) v) (f it))) v p).
Proof.
  induction m; intros.
  - apply emp_timeless.
  - inv IH. destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite struct_pred_cons2.
      apply (@bi.sep_timeless mpredI); auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
Qed.

Lemma union_pred_timeless : forall {CS : compspecs} sh m t off
  (IH : Forall (fun it : _ =>
        forall (v : reptype (t it)) (p : val),
        Timeless (data_at_rec sh (t it) v p)) m) v p,
  Timeless (union_pred m (fun (it : _) v =>
      withspacer sh (sizeof (t it)) (off it)
        (data_at_rec sh (t it) v)) v p).
Proof.
  induction m; intros.
  - apply emp_timeless.
  - inv IH. destruct m.
    + unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
    + rewrite union_pred_cons2.
      destruct v; auto.
      unfold withspacer, at_offset; simpl.
      if_tac; auto.
      apply (@bi.sep_timeless mpredI); auto.
      unfold spacer.
      if_tac.
      * apply emp_timeless.
      * unfold at_offset; apply memory_block_timeless.
Qed.

Lemma data_at_rec_timeless : forall {CS : compspecs} sh t v p,
  Timeless (data_at_rec sh t v p).
Proof.
  intros ???.
  type_induction.type_induction t; intros; rewrite data_at_rec_eq; try apply timeless_FF.
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - simple_if_tac; [apply memory_block_timeless | apply mapsto_timeless].
  - apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI)|].
    rewrite Z.sub_0_r.
    forget (Z.to_nat (Z.max 0 z)) as n.
    set (lo := 0) at 1.
    clearbody lo.
    revert lo; induction n; simpl; intros.
    + apply emp_timeless.
    + apply (@bi.sep_timeless mpredI), IHn.
      unfold at_offset; apply IH.
  - apply struct_pred_timeless; auto.
  - apply union_pred_timeless; auto.
Qed.

#[export] Instance field_at_timeless : forall {CS : compspecs} sh t gfs v p, Timeless (field_at sh t gfs v p).
Proof.
  intros; apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply data_at_rec_timeless].
Qed.

Definition funspec_sub' (f1 f2 : funspec): Prop :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall ts2 x2 (gargs:argsEnviron),
        ((!! (argsHaveTyps(snd gargs)(fst tpsig1)) && P2 ts2 x2 gargs)
         |-- |={⊤}=> (EX ts1:_,  EX x1:_, EX F:_, 
                           (F * (P1 ts1 x1 gargs)) &&
                               (!! (forall rho',
                                           ((!!(ve_of rho' = Map.empty (Values.block * type))) &&
                                                 (F * (Q1 ts1 x1 rho')))
                                         |-- (Q2 ts2 x2 rho')))))
    end
end.

Lemma coPset_to_Ensemble_top : coPset_to_Ensemble ⊤ = Ensembles.Full_set.
Proof.
  unfold coPset_to_Ensemble; apply Ensembles.Extensionality_Ensembles; split; intros ? Hin; unfold Ensembles.In in *.
  - constructor.
  - set_solver.
Qed.

Lemma prove_funspec_sub : forall f1 f2, funspec_sub' f1 f2 -> funspec_sub f1 f2.
Proof.
  unfold funspec_sub', funspec_sub; intros.
  destruct f1, f2.
  destruct H as [? H]; split; auto; intros.
  eapply derives_trans; [apply H|].
  unfold fupd, bi_fupd_fupd; simpl.
  rewrite coPset_to_Ensemble_top.
  apply derives_refl.
Qed.

Lemma fupd_eq : ghost_seplog.fupd Ensembles.Full_set Ensembles.Full_set = fupd ⊤ ⊤.
Proof.
  unfold fupd, bi_fupd_fupd; simpl. rewrite coPset_to_Ensemble_top; auto.
Qed.

Section FancyUpdates.

Local Open Scope logic_upd.

Lemma fview_shift_nonexpansive : forall E1 E2 P Q n,
  approx n (P -* |={E1,E2}=> Q) = approx n (approx n P -* |={E1,E2}=> approx n Q).
Proof.
  intros.
  rewrite wand_nonexpansive; setoid_rewrite wand_nonexpansive at 3.
  rewrite approx_idem; f_equal; f_equal.
  apply fupd_nonexpansive.
Qed.

End FancyUpdates.

Section Invariants.

Lemma fupd_timeless' : forall E1 E2 P Q, Timeless P -> (P |-- |={E1,E2}=> Q) ->
  |> P |-- |={E1,E2}=> Q.
Proof.
  intros.
  iIntros ">P"; iApply H0; auto.
Qed.

Lemma bupd_except_0 : forall P, (|==> bi_except_0 P) |-- bi_except_0 (|==> P).
Proof.
  intros; constructor; change (predicates_hered.derives (own.bupd (bi_except_0 P)) (bi_except_0 (own.bupd P : mpred))).
  intros ??; simpl in H.
  destruct (level a) eqn: Hl.
  + left.
    change ((|> FF)%pred a).
    intros ? Hl'%laterR_level.
    rewrite Hl in Hl'; apply Nat.nlt_0_r in Hl'; contradiction Hl'.
  + right.
    rewrite <- Hl in *.
    intros ? J; specialize (H _ J) as (? & ? & a' & ? & ? & ? & HP); subst.
    do 2 eexists; eauto; do 2 eexists; eauto; repeat split; auto.
    destruct HP as [Hfalse|]; auto.
    destruct (levelS_age a' n) as (a'' & Hage & ?); [lia|].
    exfalso; apply (Hfalse a'').
    constructor; auto.
Qed.

(*Lemma fupd_prop' : forall E1 E2 E2' P Q, subseteq E1 E2 ->
  ((Q |-- (|={E1,E2'}=> !!P)) ->
  (|={E1, E2}=> Q) |-- |={E1}=> !!P && (|={E1, E2}=> Q))%I.
Proof.
  unfold updates.fupd, bi_fupd_fupd; simpl.
  unfold fupd; intros ?????? HQ.
  iIntros "H Hpre".
  iMod ("H" with "Hpre") as ">(Hpre & Q)".
  erewrite ghost_set_subset with (s' := coPset_to_Ensemble E1).
  iDestruct "Hpre" as "(wsat & en1 & en2)".
  iCombine ("wsat en1 Q") as "Q".
  erewrite (add_andp (_ ∗ _ ∗ Q)%I (bi_except_0 (!! P))) at 1.
  rewrite sepcon_andp_prop bi.except_0_and.
  iModIntro; iSplit.
  { iDestruct "Q" as "[? ?]"; auto. }
  iDestruct "Q" as "[($ & $ & $) _]"; iFrame; auto.
  { iIntros "(? & ? & Q)".
    setoid_rewrite <- (own.bupd_prop P).
    iApply bupd_except_0.
    iMod (HQ with "Q [$]") as ">(? & ?)"; auto. }
  { intro a; destruct (coPset_elem_of_dec (Pos.of_nat (S a)) E1); auto. }
  { unfold coPset_to_Ensemble; intros ??; unfold In in *; auto. }
Qed.

Lemma fupd_prop : forall E1 E2 P Q, subseteq E1 E2 ->
  (Q |-- !!P) ->
  ((|={E1, E2}=> Q) |-- |={E1}=> !!P && (|={E1, E2}=> Q))%I.
Proof.
  intros; eapply fupd_prop'; auto.
  eapply derives_trans; eauto.
  apply fupd_intro.
Qed.*)

Global Opaque updates.fupd.

Definition cinv (N : namespace) g (P : mpred) : mpred := inv N (P || cinv_own g Tsh).

Lemma cinv_alloc_dep : forall N E P, (ALL g, |> P g) |-- |={E}=> EX g : _, cinv N g (P g) * cinv_own g Tsh.
Proof.
  intros; iIntros "HP".
  iMod (own_alloc(RA := share_ghost) with "[$]") as (g) "?"; first done.
  iExists g.
  iMod (inv_alloc with "[HP]"); last by iFrame.
  iNext; iLeft; auto.
Qed.

Lemma cinv_alloc : forall N E P, |> P |-- |={E}=> EX g : _, cinv N g P * cinv_own g Tsh.
Proof.
  intros; iIntros "HP".
  iApply cinv_alloc_dep.
  iIntros (_); auto.
Qed.

Lemma make_cinv : forall N E P Q, (P |-- Q) -> P |-- |={E}=> EX g : _, cinv N g Q * cinv_own g Tsh.
Proof.
  intros.
  eapply derives_trans, cinv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

Lemma cinv_cancel : forall N E g P,
  ↑N ⊆ E -> cinv N g P * cinv_own g Tsh |-- |={E}=> (|> P).
Proof.
  intros; iIntros "[#I g]".
  iInv "I" as "H" "Hclose".
  iDestruct "H" as "[$ | >g']".
  - iApply "Hclose"; iRight; auto.
  - iDestruct (cinv_own_excl with "[$g $g']") as "[]"; auto with share.
Qed.

(* These seem reasonable, but for some reason cause iInv to hang if exported. *)
#[local] Instance into_inv_cinv N g P : IntoInv (cinv N g P) N := {}.

#[local] Instance into_acc_cinv E N g P p :
  IntoAcc (X:=unit) (cinv N g P)
          (↑N ⊆ E /\ p <> Share.bot) (cinv_own g p) (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
          (λ _, ▷ P ∗ cinv_own g p)%I (λ _, ▷ P)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor; intros [].
  iIntros "#I g".
  iInv "I" as "H" "Hclose".
  iDestruct "H" as "[$ | >g']".
  - iFrame "g"; iExists tt; iIntros "!> HP".
    iApply "Hclose"; iLeft; auto.
  - iDestruct (cinv_own_excl with "[$g' $g]") as "[]"; auto.
Qed.

Lemma cinv_nonexpansive : forall N g, nonexpansive (cinv N g).
Proof.
  intros; apply inv_nonexpansive2.
  apply @disj_nonexpansive, const_nonexpansive.
  apply identity_nonexpansive.
Qed.

Lemma cinv_nonexpansive2 : forall N g f, nonexpansive f ->
  nonexpansive (fun a => cinv N g (f a)).
Proof.
  intros; apply inv_nonexpansive2.
  apply @disj_nonexpansive, const_nonexpansive; auto.
Qed.

End Invariants.

(* avoids some fragility in tactics *)
Definition except0 : mpred -> mpred := bi_except_0.

Lemma replace_SEP'_fupd:
 forall n R' Espec {cs: compspecs} Delta P Q Rs c Post,
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (canon.my_nth n Rs TT ::  nil))) |-- liftx (|={⊤}=> R') ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (canon.replace_nth n Rs R')))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx Rs))) c Post.
Proof.
intros; eapply replace_SEP'_fupd; eauto.
rewrite fupd_eq; auto.
Qed.

Tactic Notation "viewshift_SEP" constr(n) constr(R) :=
  first [apply (replace_SEP'_fupd (Z.to_nat n) R) | apply (replace_SEP''_fupd (Z.to_nat n) R)];
  unfold canon.my_nth,canon.replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Tactic Notation "viewshift_SEP" constr(n) constr(R) "by" tactic1(t):=
  first [apply (replace_SEP'_fupd (Z.to_nat n) R) | apply (replace_SEP''_fupd (Z.to_nat n) R)];
  unfold canon.my_nth,canon.replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota; [ now t | ].

Ltac ghost_alloc G ::=
  match goal with |-semax _ (PROPx _ (LOCALx _ (SEPx (?R1 :: _)))) _ _ =>
    rewrite <- (emp_sepcon R1) at 1; Intros; viewshift_SEP 0 (EX g : _, G g);
  [go_lowerx; eapply derives_trans, bupd_fupd; rewrite ?emp_sepcon;
   apply own_alloc; auto; simpl; auto with init share ghost|] end.

Ltac ghosts_alloc G n ::=
  match goal with |-semax _ (PROPx _ (LOCALx _ (SEPx (?R1 :: _)))) _ _ =>
    rewrite <- (emp_sepcon R1) at 1; Intros; viewshift_SEP 0 (EX lg : _, !!(Zlength lg = n) && iter_sepcon G lg);
  [go_lowerx; eapply derives_trans, bupd_fupd; rewrite ?emp_sepcon;
   apply own_list_alloc'; auto; simpl; auto with init share ghost|] end.
