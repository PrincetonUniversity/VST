Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.ghost.
Require Import Ensembles.

Local Open Scope logic.

Class BupdSepLog (A N D: Type) {ND: NatDed A}{SL: SepLog A} := mkBSL {
  bupd: A -> A;
  inG: Ghost -> A;
  own: forall {RA: Ghost}, N -> G -> D -> A;
  bupd_intro: forall P, P |-- bupd P;
  bupd_mono: forall P Q, P |-- Q -> bupd P |-- bupd Q;
  bupd_trans: forall P, bupd (bupd P) |-- bupd P;
  bupd_frame_r: forall P Q, bupd P * Q |-- bupd (P * Q);
  own_alloc: forall {RA: Ghost} a pp, (exists b, joins a b) ->
    inG RA |-- bupd (EX g: N, own g a pp);
  own_op: forall {RA: Ghost} g (a1 a2 a3: G) pp, join a1 a2 a3 ->
    own g a3 pp = own g a1 pp * own g a2 pp;
  own_valid: forall {RA: Ghost} g (a1 a2: G) pp,
    own g a1 pp * own g a2 pp |-- !!joins a1 a2;
  own_update_ND: forall {RA: Ghost} g (a: G) B pp, fp_update_ND a B ->
    own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp);
  own_update: forall {RA: Ghost} g (a: G) b pp, fp_update a b ->
    own g a pp |-- bupd (own g b pp);
  inG_emp: forall RA, inG RA |-- emp;
  inG_dup: forall RA, inG RA |-- inG RA * inG RA
  }.

Notation "|==> P" := (bupd P) (at level 62): logic.

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

Instance LiftBupdSepLog (A B N D: Type) {NB: NatDed B}{SB: SepLog B}{BSLB: BupdSepLog B N D} :
  BupdSepLog (A -> B) N D.
 apply (mkBSL _ _ _ _ _ (fun P rho => |==> P rho) (fun RA rho => inG RA)
   (fun RA g a pp rho => own g a pp)); repeat intro; simpl.
 apply bupd_intro.
 apply bupd_mono; auto.
 apply bupd_trans.
 apply bupd_frame_r.
 apply own_alloc; auto.
 extensionality rho; apply own_op; auto.
 apply own_valid.
 apply own_update_ND; auto.
 apply own_update; auto.
 apply inG_emp.
 apply inG_dup.
Defined.
