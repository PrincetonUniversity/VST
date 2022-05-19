Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.ghost.
Require Import Ensembles List.

Local Open Scope logic.

Definition pred_infinite {N} (P : N -> Prop) := forall l, exists x, ~In x l /\ P x.

(* c.f. https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/bi/updates.v *)
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

Declare Scope logic_upd. (* so we can close this scope when we import Iris *)

Open Scope logic_upd.

Notation "|==> P" := (bupd P) (at level 99, P at level 200): logic_upd.

Section bupd_derived.

Context `{BUPD : BupdSepLog}.

Lemma bupd_orp_r: forall (P Q: A), ((|==> P) || Q) |-- |==> P || Q.
Proof.
  intros.
  apply orp_left.
  + apply bupd_mono.
    apply orp_right1, derives_refl.
  + eapply derives_trans; [| apply bupd_intro].
    apply orp_right2, derives_refl.
Qed.

Lemma bupd_orp_l: forall (P Q: A), (P || |==> Q) |-- |==> P || Q.
Proof.
  intros; rewrite orp_comm, (orp_comm P Q); apply bupd_orp_r.
Qed.

Lemma bupd_orp: forall (P Q: A), ((|==> P) || |==> Q) |-- |==> P || Q.
Proof.
  intros.
  eapply derives_trans, bupd_trans.
  eapply derives_trans; [apply bupd_orp_l|].
  apply bupd_mono, bupd_orp_r.
Qed.

Lemma bupd_frame_l: forall (P Q: A), (P * |==> Q) |-- |==> P * Q.
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm P Q); apply bupd_frame_r.
Qed.

Lemma bupd_sepcon: forall (P Q: A), ((|==> P) * |==> Q) |-- |==> P * Q.
Proof.
  intros.
  eapply derives_trans, bupd_trans.
  eapply derives_trans; [apply bupd_frame_l|].
  apply bupd_mono, bupd_frame_r.
Qed.

Lemma own_alloc: forall {RA: Ghost} (a: G) pp,
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

Lemma own_update: forall {RA: Ghost} g (a: G) b pp, fp_update a b ->
    own g a pp |-- |==> (own g b pp).
Proof.
  intros.
  eapply derives_trans; [apply own_update_ND with (B := Singleton _ b)|].
  - intros ? J; destruct (H _ J).
    do 2 eexists; [constructor | eauto].
  - apply bupd_mono.
    apply exp_left; intro.
    rewrite imp_andp_adjoint; apply prop_left; intro X.
    inversion X; auto.
    rewrite <- imp_andp_adjoint; apply andp_left2, derives_refl.
Qed.

Lemma own_valid: forall {RA: Ghost} g (a: G) pp,
  own g a pp |-- !!valid a.
Proof.
  intros.
  erewrite own_op by apply core_unit.
  eapply derives_trans; [apply own_valid_2|].
  apply prop_left; intros (a' & J & ?); apply prop_right.
  assert (a = a') as ->; auto.
  eapply join_eq; eauto; apply core_unit.
Qed.

Lemma own_sub: forall {RA: Ghost} g (a b: G) pp,
  join_sub b a ->
  own g a pp |-- |==> own g b pp.
Proof.
  intros; apply own_update, fp_update_sub; auto.
Qed.

Lemma own_core: forall {RA: Ghost} g (a: G) pp,
  own g a pp |-- |==> own g (core a) pp.
Proof.
  intros; apply own_sub.
  eexists; apply core_unit.
Qed.

End bupd_derived.

#[global] Instance LiftBupdSepLog (A B N D: Type) {NB: NatDed B}{SB: SepLog B}{BSLB: BupdSepLog B N D} :
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

Class FupdSepLog (A N D I: Type) {ND: NatDed A}{IA: Indir A}{SL: SepLog A}{BSL: BupdSepLog A N D} := mkFSL {
  fupd: Ensemble I -> Ensemble I -> A -> A;
  fupd_mask_union: forall E1 E2, Disjoint _ E1 E2 ->
    emp |-- fupd (Union _ E1 E2) E2 (fupd E2 (Union _ E1 E2) emp);
  except_0_fupd: forall E1 E2 P, ((|> FF) || fupd E1 E2 P) |-- fupd E1 E2 P;
  fupd_mono: forall E1 E2 P Q, (P |-- Q) -> fupd E1 E2 P |-- fupd E1 E2 Q;
  fupd_trans: forall E1 E2 E3 P, fupd E1 E2 (fupd E2 E3 P) |-- fupd E1 E3 P;
  fupd_mask_frame_r': forall E1 E2 Ef P, Disjoint _ E1 Ef ->
    fupd E1 E2 (!! (Disjoint _ E2 Ef) --> P) |-- fupd (Union _ E1 Ef) (Union _ E2 Ef) P;
  fupd_frame_r: forall E1 E2 P Q, (fupd E1 E2 P) * Q |-- fupd E1 E2 (P * Q);
  bupd_fupd: forall E P, bupd P |-- fupd E E P
  }.

Notation "|={ E1 , E2 }=> P" := (fupd E1 E2 P) (at level 99, E1 at level 50, E2 at level 50, P at level 200): logic_upd.
Notation "|={ E }=> P" := (fupd E E P) (at level 99, E at level 50, P at level 200): logic_upd.

Lemma Empty_set_Union : forall {A} S, Union A (Empty_set A) S = S.
Proof.
  intros; apply Extensionality_Ensembles; split; intros ? H.
  - inversion H; auto; contradiction.
  - constructor 2; auto.
Qed.

Lemma Union_Empty_set : forall {A} S, Union A S (Empty_set A) = S.
Proof.
  intros; apply Extensionality_Ensembles; split; intros ? H.
  - inversion H; auto; contradiction.
  - constructor 1; auto.
Qed.

Lemma Empty_set_disjoint1 : forall {A} (E : Ensemble A), Disjoint _ (Empty_set _) E.
Proof.
  constructor; intros.
  intros Hin; inversion Hin; subst; contradiction.
Qed.

Lemma Empty_set_disjoint2 : forall {A} (E : Ensemble A), Disjoint _ E (Empty_set _).
Proof.
  constructor; intros.
  intros Hin; inversion Hin; subst; contradiction.
Qed.

Section fupd_derived.

Context `{FUPD : FupdSepLog}.

Lemma fupd_mask_intro_union {CA : ClassicalSep A} E1 E2 P : Disjoint _ E1 E2 ->
  P |-- |={Union _ E1 E2,E2}=> |={E2,Union _ E1 E2}=> P.
Proof.
  intros.
  rewrite <- (sepcon_emp P), sepcon_comm.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply fupd_mask_union; eauto|].
  eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
  apply fupd_frame_r.
Qed.

Lemma fupd_intro {CA : ClassicalSep A} E P : P |-- |={E}=> P.
Proof.
  eapply derives_trans, fupd_trans.
  eapply derives_trans; [apply (fupd_mask_intro_union (Empty_set _))|].
  { apply Empty_set_disjoint1. }
  rewrite Empty_set_Union. apply derives_refl.
Qed.

Lemma fupd_except_0 {CA : ClassicalSep A} E1 E2 (P : A) : (|={E1,E2}=> ((|> FF) || P)) |-- |={E1,E2}=> P.
Proof.
  eapply derives_trans; [apply fupd_mono|].
  { apply orp_left; [apply orp_right1, derives_refl | apply orp_right2, fupd_intro]. }
  eapply derives_trans; [apply fupd_mono, except_0_fupd|].
  apply fupd_trans.
Qed.

Lemma fupd_idem E P {CA : ClassicalSep A} : (|={E}=> |={E}=> P) = |={E}=> P.
Proof.
  apply pred_ext.
  - apply fupd_trans.
  - apply fupd_intro.
Qed.

Lemma fupd_frame_l E1 E2 P Q : (P * |={E1,E2}=> Q) |-- |={E1,E2}=> P * Q.
Proof.
  rewrite !(sepcon_comm P); apply fupd_frame_r.
Qed.

Lemma fupd_mask_intro {CA : ClassicalSep A} E1 E2 P : Disjoint _ E1 E2 ->
  ((|={E2,Union _ E1 E2}=> emp) -* P) |-- |={Union _ E1 E2,E2}=> P.
Proof.
  intros.
  rewrite <- sepcon_emp at 1.
  eapply derives_trans; [apply sepcon_derives, fupd_mask_intro_union; eauto; apply derives_refl|].
  eapply derives_trans, fupd_mono; [apply fupd_frame_l|].
  rewrite wand_sepcon_adjoint; apply derives_refl.
Qed.

Lemma fupd_mask_intro_all {CA : ClassicalSep A} E P :
  ((|={Empty_set _,E}=> emp) -* P) |-- |={E,Empty_set _}=> P.
Proof.
  intros.
  rewrite <- (Union_Empty_set E); apply fupd_mask_intro.
  apply Empty_set_disjoint2.
Qed.

Lemma fupd_elim E1 E2 E3 P Q :
    Q |-- (|={E2,E3}=> P) -> (|={E1,E2}=> Q) |-- (|={E1,E3}=> P).
Proof.
  intros.
  eapply derives_trans; [apply fupd_mono, H|].
  apply fupd_trans.
Qed.

Lemma fupd_mask_frame_r E1 E2 Ef P :
  Disjoint _ E1 Ef -> (|={E1,E2}=> P) |-- |={Union _ E1 Ef, Union _ E2 Ef}=> P.
Proof.
  intros.
  eapply derives_trans, fupd_mask_frame_r'; auto.
  apply fupd_mono.
  rewrite <- imp_andp_adjoint.
  apply andp_left1, derives_refl.
Qed.

Lemma fupd_or E1 E2 P Q :
    (|={E1,E2}=> P) || (|={E1,E2}=> Q) |-- (|={E1,E2}=> (P || Q)).
Proof.
  apply orp_left; apply fupd_mono; [apply orp_right1 | apply orp_right2]; apply derives_refl.
Qed.

Lemma fupd_and E1 E2 P Q :
    (|={E1,E2}=> (P && Q)) |-- (|={E1,E2}=> P) && (|={E1,E2}=> Q).
Proof.
  apply andp_right; apply fupd_mono; [apply andp_left1 | apply andp_left2]; apply derives_refl.
Qed.

Lemma fupd_exists E1 E2 T (P : T -> A) : (EX x : T, |={E1, E2}=> P x) |-- |={E1, E2}=> EX x : T, P x.
Proof.
  apply exp_left; intros x.
  apply fupd_mono.
  apply exp_right with x, derives_refl.
Qed.

Lemma fupd_forall E1 E2 T (P : T -> A) : (|={E1, E2}=> ALL x : T, P x) |-- ALL x : T, |={E1, E2}=> P x.
Proof.
  apply allp_right; intros x.
  apply fupd_mono.
  apply allp_left with x, derives_refl.
Qed.

Lemma fupd_sep E P Q : (|={E}=> P) * (|={E}=> Q) |-- |={E}=> P * Q.
Proof.
  eapply derives_trans; [apply fupd_frame_r|].
  eapply derives_trans, fupd_trans; apply fupd_mono.
  apply fupd_frame_l.
Qed.

End fupd_derived.

#[global] Instance LiftFupdSepLog (A B N D I: Type) {NB: NatDed B}{IB: Indir B}{SB: SepLog B}{BSLB: BupdSepLog B N D}{FSLB: FupdSepLog B N D I} :
  FupdSepLog (A -> B) N D I.
 apply (mkFSL _ _ _ _ _ _ _ _ (fun E1 E2 P rho => |={E1,E2}=> P rho));
   repeat intro; simpl.
 apply fupd_mask_union; auto.
 apply except_0_fupd.
 apply fupd_mono; auto.
 apply fupd_trans.
 apply fupd_mask_frame_r'; auto.
 apply fupd_frame_r.
 apply bupd_fupd.
Defined.
