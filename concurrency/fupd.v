From stdpp Require Export namespaces coPset.
From VST.veric Require Import compcert_rmaps fupd.
From VST.msl Require Import ghost ghost_seplog sepalg_generators.
From VST.concurrency Require Import ghosts conclib invariants cancelable_invariants.
Require Export VST.veric.bi.
Import Ensembles.
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

#[export] Instance data_at_timeless : forall {CS : compspecs} sh t v p, Timeless (data_at sh t v p).
Proof.
  intros; apply (@bi.and_timeless mpredI); [apply (@bi.pure_timeless mpredI) | apply data_at_rec_timeless].
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

Lemma inv_alloc : forall E P, |> P |-- |={E}=> EX i : _, inv i P.
Proof.
  intros; eapply derives_trans, fupd_mono; [apply inv_alloc|].
  iIntros "I"; iDestruct "I" as (i) "I".
  unfold inv; iExists _, i; iFrame; auto.
Qed.

Lemma make_inv : forall E P Q, (P |-- Q) -> P |-- |={E}=> EX i : _, inv i Q.
Proof.
  intros.
  eapply derives_trans, inv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

(*Lemma make_inv' : forall P Q, (P |-- Q) -> (wsat * P |-- |==> EX i : _, |> (wsat * (inv i Q)))%I.
Proof.
  intros.
  iIntros "[wsat P]".
  iPoseProof (make_inv empty _ _ H with "P") as "inv".
  iMod (wsat_fupd_elim with "[$wsat $inv]") as "[wsat inv]".
  iDestruct "inv" as (i) "inv"; iExists i.
  unfold bi_except_0.
  iIntros "!> !>".
  iDestruct "wsat" as "[? | $]"; auto.
  iDestruct "inv" as "[? | ?]"; auto.
Qed.

Lemma inv_close_aux : forall E (i : iname) P,
  (ghost_list(P := token_PCM) g_dis (list_singleton i (Some tt)) * inv i P * |> P *
  (wsat * ghost_set g_en (Subtract E i))
  |-- |==> bi_except_0 (wsat * (ghost_set g_en (Singleton i) * ghost_set g_en (Subtract E i))))%I.
Proof.
  intros.
  iIntros "(((? & ?) & ?) & ? & en)".
  iMod (wsat_close with "[-en]") as "[$ $]"; iFrame; auto.
Qed.*)

(* hack because we don't have namespaces in wsat *)
Definition to_coPset (N : namespace) : coPset :=
  match N with
  | [p] => {[p]}
  | _ => ∅
  end.

Lemma coPset_to_Ensemble_minus : forall E1 E2, coPset_to_Ensemble (E1 ∖ E2) = Setminus (coPset_to_Ensemble E1) (coPset_to_Ensemble E2).
Proof.
  intros; unfold coPset_to_Ensemble.
  apply Extensionality_Ensembles; split; intros ? Hin; unfold In in *.
  - apply elem_of_difference in Hin as []; constructor; auto.
  - inv Hin. apply elem_of_difference; auto.
Qed.

Lemma coPset_to_Ensemble_single : forall x, coPset_to_Ensemble {[Pos.of_nat (S x)]} = Singleton x.
Proof.
  intros; unfold coPset_to_Ensemble.
  apply Extensionality_Ensembles; split; intros ? Hin; unfold In in *.
  - apply elem_of_singleton in Hin.
    apply (f_equal Pos.to_nat) in Hin.
    rewrite -> !Nat2Pos.id in Hin by auto; inv Hin; constructor.
  - inv Hin.
    apply elem_of_singleton; auto.
Qed.

Lemma Union_Readd : forall {A} E (x : A), EqDec A -> In E x ->
  Union (Subtract E x) (Singleton x) = E.
Proof.
  intros; apply Extensionality_Ensembles; split; intros ? Hin.
  - inv Hin; auto.
    + inv H0; auto.
    + inv H0; auto.
  - destruct (eq_dec x x0).
    + subst; constructor 2; constructor.
    + constructor 1; constructor; auto.
      intros Hs; inv Hs; auto.
Qed.

#[export] Instance into_acc_inv N P E:
  IntoAcc (X := unit) (inv N P)
          (to_coPset N ⊆ E) emp (updates.fupd E (E ∖ to_coPset N)) (updates.fupd (E ∖ to_coPset N) E)
          (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
Proof.
  rewrite /inv /IntoAcc /accessor bi.exist_unit.
  intros; unfold bi_entails, bi_wand, fupd, bi_fupd_fupd; simpl.
  Intros i; subst.
  unfold to_coPset in *; rewrite -> ndot_eq in *; simpl in *.
  sep_apply (inv_open (coPset_to_Ensemble E)).
  { unfold coPset_to_Ensemble, In; apply elem_of_subseteq_singleton, H. }
  rewrite -wand_sepcon_adjoint sepcon_emp.
  rewrite coPset_to_Ensemble_minus coPset_to_Ensemble_single.
  apply derives_refl.
Qed.

Definition cinv (N : namespace) g P := EX i : iname, !!(N = nroot .@ (Pos.of_nat (S i))) && cinvariant i g P.

Lemma cinv_alloc : forall E P, |> P |-- |={E}=> EX i : _, EX g : _, cinv i g P * cinv_own g Tsh.
Proof.
  intros; eapply derives_trans, fupd_mono; [apply cinv_alloc|].
  unfold bi_entails, cinv; simpl.
  Intros i g; EExists; Exists g i; entailer!.
Qed.

Lemma make_cinv : forall E P Q, (P |-- Q) -> P |-- |={E}=> EX i : _, EX g : _, cinv i g Q * cinv_own g Tsh.
Proof.
  intros.
  eapply derives_trans, cinv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

(* These seem reasonable, but for some reason cause iInv to hang if exported. *)
#[local] Instance into_inv_cinv N g P : IntoInv (cinv N g P) N := {}.

#[local] Instance into_acc_cinv E N g P p :
  IntoAcc (X:=unit) (cinv N g P)
          (to_coPset N ⊆ E /\ p <> Share.bot) (cinv_own g p) (fupd E (E ∖ to_coPset N)) (fupd (E ∖ to_coPset N) E)
          (λ _, ▷ P ∗ cinv_own g p)%I (λ _, ▷ P)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor; intros [].
  unfold bi_entails, fupd, bi_fupd_fupd, bi_wand, cinv; simpl.
  Intros i; subst.
  unfold to_coPset in *; rewrite -> ndot_eq in *; simpl in *.
  rewrite -wand_sepcon_adjoint.
  sep_apply (cinv_open (coPset_to_Ensemble E)).
  { unfold coPset_to_Ensemble, In; apply elem_of_subseteq_singleton, H. }
  rewrite coPset_to_Ensemble_minus coPset_to_Ensemble_single.
  rewrite bi.exist_unit; apply derives_refl.
Qed.

End Invariants.

(* avoids some fragility in tactics *)
Definition except0 : mpred -> mpred := bi_except_0.

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

Lemma coPset_to_Ensemble_top : coPset_to_Ensemble ⊤ = Full_set.
Proof.
  unfold coPset_to_Ensemble; apply Extensionality_Ensembles; split; intros ? Hin; unfold In in *.
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

Global Opaque updates.fupd.

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
