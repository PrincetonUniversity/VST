Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghost.
Require Import VST.progs.conclib.

(* Where should this sit? *)

Section Invariants.

Instance unit_PCM : Ghost := { valid a := True; Join_G := Join_equiv unit }.
Proof. auto. Defined.

Instance unit_order : PCM_order (@eq unit).
Proof.
  split; try typeclasses eauto.
  - intros; subst.
    exists c; repeat split; auto.
  - intros; inv H; auto.
  - intros; split; auto.
Qed.

Definition agree g sh (pp : preds) :=
  @own _ _ _ _ _ _ snap_PCM g (sh, tt) pp.

Program Definition approx_equiv (P Q : preds) : pred rmap :=
  fun w => preds_fmap (approx (level w)) (approx (level w)) P =
           preds_fmap (approx (level w)) (approx (level w)) Q.
Next Obligation.
  intros ????.
  assert (level a >= level a')%nat by (apply age_level in H; omega).
  replace (preds_fmap _ _) with (preds_fmap (approx (level a')) (approx (level a')) oo
    preds_fmap (approx (level a)) (approx (level a))).
  simpl; rewrite H0; auto.
  setoid_rewrite preds_fmap_comp; rewrite approx_oo_approx', approx'_oo_approx; auto.
Defined.

Lemma agree_eq : forall g sh1 sh2 P Q, agree g sh1 P * agree g sh2 Q |-- approx_equiv P Q.
Proof.
  intros.
  change (predicates_hered.derives (agree g sh1 P * agree g sh2 Q) (approx_equiv P Q)).
  intros ? (? & ? & J & (H1 & ? & Hg1) & (H2 & ? & Hg2)); simpl in *.
  destruct (join_level _ _ _ J).
  apply ghost_of_join in J.
  rewrite Hg1, Hg2, !own.ghost_fmap_singleton in J.
  apply own.singleton_join_inv in J as (? & J & ?).
  destruct J as [_ J]; simpl in J.
  assert (H2 = H1) by apply proof_irr; subst.
  repeat replace (level _) with (level a) in * by omega.
  inv J; auto.
Qed.

Definition agree_auth g (P : mpred) :=
  @own _ _ _ _ _ _ snap_PCM g (Tsh, tt) (SomeP rmaps.Mpred (fun _ => P)).

Definition agree_snap g (P : mpred) :=
  @own _ _ _ _ _ _ snap_PCM g (Share.bot, tt) (SomeP rmaps.Mpred (fun _ => P)).

(* Our ghost state construction makes it awkward to put agree inside other ghost state constructions.
   As a workaround, instead of having one ghost location with a map from indices to agrees,
   we have a map from indices to ghost locations, each with an agree. *)
Class invG := { g_inv : Z -> gname; g_dis : Z -> gname; g_en : Z -> gname }.

Context {inv_names : invG}.

Definition wsat : mpred := EX I : list mpred,
  fold_right sepcon emp (map (fun i => agree_auth (g_inv i) (Znth i I)) (upto (length I))) *
  fold_right sepcon emp (map (fun i => (|> Znth i I * excl (g_dis i) i) || excl (g_en i) i) (upto (length I))).

Definition invariant i P : mpred := agree_snap (g_inv i) P.

Lemma wsat_alloc : forall P, wsat * |> P |-- |==> wsat * EX i : _, invariant i P.
Proof.
  intro; unfold wsat.
  Intros I.
  rewrite <- emp_sepcon at 1; eapply derives_trans; [apply sepcon_derives, derives_refl|].
  { apply (own_alloc(RA := @snap_PCM _ _ unit_order) (Tsh, tt) (SomeP rmaps.Mpred (fun _ => P))).
    simpl; auto. }
  eapply derives_trans; [apply bupd_frame_r|].
  eapply derives_trans, bupd_trans; apply bupd_mono.
  Intros gi.
  intro; change (predicates_hered.derives (wsat * |> P) (|==> wsat * EX i : _, invariant i P)).
  intros ? (? & ? & ? & (I & ? & ? & ? & Hagree & Htokens) & ?).

(* define fancy update, prove invariant rules *)

(* Consider putting invariants and fancy updates in msl (a la ghost_seplog), and these proofs in
   veric (a la own). *)

End Invariants.
