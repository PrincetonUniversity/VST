Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.ghost.
Require Import List.

Local Open Scope logic.

Definition pred_infinite {N} (P : N -> Prop) := forall l, exists x, ~In x l /\ P x.

Class BupdSepLog (A N D: Type) {ND: NatDed A}{SL: SepLog A} := mkBSL {
  bupd: A -> A;
  own: forall {RA: Ghost}, N -> G -> D -> A;
  infinite_names: forall (l : list N), exists x, ~In x l;
  bupd_intro: forall P, P |-- bupd P;
  bupd_mono: forall P Q, (P |-- Q) -> bupd P |-- bupd Q;
  bupd_trans: forall P, bupd (bupd P) |-- bupd P;
  bupd_frame_r: forall P Q, bupd P * Q |-- bupd (P * Q);
  own_alloc_strong: forall {RA: Ghost} P a pp, pred_infinite P -> valid a ->
    emp |-- bupd (EX g: N, !!(P g) && own g a pp);
  own_op: forall {RA: Ghost} g (a1 a2 a3: G) pp, join a1 a2 a3 ->
    own g a3 pp = own g a1 pp * own g a2 pp;
  own_valid_2: forall {RA: Ghost} g (a1 a2: G) pp,
    own g a1 pp * own g a2 pp |-- !!valid_2 a1 a2;
  own_update_ND: forall {RA: Ghost} g (a: G) B pp, fp_update_ND a B ->
    own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp);
  own_dealloc: forall {RA: Ghost} g (a: G) pp,
    own g a pp |-- emp
  }.

Notation "|==> P" := (bupd P) (at level 99, P at level 200): logic.

Lemma bupd_orp_r: forall `{BupdSepLog} (P Q: A), ((|==> P) || Q) |-- |==> P || Q.
Proof.
  intros.
  apply orp_left.
  + apply bupd_mono.
    apply orp_right1, derives_refl.
  + eapply derives_trans; [| apply bupd_intro].
    apply orp_right2, derives_refl.
Qed.

Lemma bupd_orp_l: forall `{BupdSepLog} (P Q: A), (P || |==> Q) |-- |==> P || Q.
Proof.
  intros; rewrite orp_comm, (orp_comm P Q); apply bupd_orp_r.
Qed.

Lemma bupd_orp: forall `{BupdSepLog} (P Q: A), ((|==> P) || |==> Q) |-- |==> P || Q.
Proof.
  intros.
  eapply derives_trans, bupd_trans.
  eapply derives_trans; [apply bupd_orp_l|].
  apply bupd_mono, bupd_orp_r.
Qed.

Lemma bupd_frame_l: forall `{BupdSepLog} (P Q: A), (P * |==> Q) |-- |==> P * Q.
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm P Q); apply bupd_frame_r.
Qed.

Lemma bupd_sepcon: forall `{BupdSepLog} (P Q: A), ((|==> P) * |==> Q) |-- |==> P * Q.
Proof.
  intros.
  eapply derives_trans, bupd_trans.
  eapply derives_trans; [apply bupd_frame_l|].
  apply bupd_mono, bupd_frame_r.
Qed.

Inductive Singleton {A} (x : A) : A -> Prop :=
| Singleton_I : Singleton x x.

Lemma own_alloc: forall `{BUPD: BupdSepLog} {RA: Ghost} (a: G) pp,
  valid a -> emp |-- bupd (EX g: N, own g a pp).
Proof.
  intros.
  eapply derives_trans; [apply (own_alloc_strong (fun _ => True)); eauto|].
  { intros ?.
    destruct (infinite_names l); eauto. }
  apply bupd_mono.
  apply exp_left; intro g; apply exp_right with g.
  apply andp_left2, derives_refl.
Qed.

Lemma own_update: forall `{BUPD: BupdSepLog} {RA: Ghost} g (a: G) b pp, fp_update a b ->
    own g a pp |-- |==> (own g b pp).
Proof.
  intros.
  eapply derives_trans; [apply own_update_ND with (B := Singleton b)|].
  - intros ? J; destruct (H _ J).
    do 2 eexists; [constructor | eauto].
  - apply bupd_mono.
    apply exp_left; intro.
    rewrite imp_andp_adjoint; apply prop_left; intro X.
    inversion X; auto.
    rewrite <- imp_andp_adjoint; apply andp_left2, derives_refl.
Qed.

Lemma own_valid: forall `{BupdSepLog} {RA: Ghost} g (a: G) pp,
  own g a pp |-- !!valid a.
Proof.
  intros.
  erewrite own_op by apply core_unit.
  eapply derives_trans; [apply own_valid_2|].
  apply prop_left; intros (a' & J & ?); apply prop_right.
  assert (a = a') as ->; auto.
  eapply join_eq; eauto; apply core_unit.
Qed.

Lemma own_sub: forall `{BupdSepLog} {RA: Ghost} g (a b: G) pp,
  join_sub b a ->
  own g a pp |-- |==> own g b pp.
Proof.
  intros; apply own_update, fp_update_sub; auto.
Qed.

Lemma own_core: forall `{BupdSepLog} {RA: Ghost} g (a: G) pp,
  own g a pp |-- |==> own g (core a) pp.
Proof.
  intros; apply own_sub.
  eexists; apply core_unit.
Qed.

(*Lemma own_core2: forall `{BupdSepLog} {RA: Ghost} g (a: G) pp,
  own g a pp |-- |==> own g (core2 a) pp.
Proof.
  intros; apply own_sub.
  eexists; apply core2_unit.
Qed.*)

Instance LiftBupdSepLog (A B N D: Type) {NB: NatDed B}{SB: SepLog B}{BSLB: BupdSepLog B N D} :
  BupdSepLog (A -> B) N D.
 apply (mkBSL _ _ _ _ _ (fun P rho => |==> P rho) (fun RA g a pp rho => own g a pp));
   repeat intro; simpl.
 apply infinite_names.
 apply bupd_intro.
 apply bupd_mono; auto.
 apply bupd_trans.
 apply bupd_frame_r.
 apply own_alloc_strong; auto.
 extensionality rho; apply own_op; auto.
 apply own_valid_2.
 apply own_update_ND; auto.
 apply own_dealloc; auto.
Defined.
