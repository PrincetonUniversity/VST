(* Specifications for locks for use with general invariants, in the style of TaDA *)
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.conclib.
Require Export VST.concurrency.invariants.
Require Export VST.concurrency.fupd.
Require Export VST.atomics.general_atomics.

Open Scope logic.

Section locks.

Context {P : Ghost}.

Definition my_half g sh (a : G) := ghost_part(P := P) sh a g.
Definition public_half g (a : G) := ghost_reference(P := P) a g.
Definition both_halves (a : G) g := ghost_part_ref(P := P) Tsh a a g.

Lemma my_half_join : forall sh1 sh2 sh a1 a2 a g, sepalg.join sh1 sh2 sh -> sepalg.join a1 a2 a -> sh1 <> Share.bot -> sh2 <> Share.bot ->
  my_half g sh1 a1 * my_half g sh2 a2 = my_half g sh a.
Proof.
  exact ghost_part_join.
Qed.

Lemma both_halves_join : forall g (a : G), my_half g Tsh a * public_half g a = both_halves a g.
Proof.
  intros.
  apply (ghost_part_ref_join(P := P)).
Qed.

Lemma public_agree : forall g (a b: G), my_half g Tsh a * public_half g b |-- !!(a = b).
Proof.
  intros. unfold my_half, public_half. eapply derives_trans; [apply ref_sub|].
  apply prop_left; intro; apply prop_right.
  rewrite if_true in H; auto.
Qed.

Lemma public_update : forall g (a b a' : G),
  my_half g Tsh a * public_half g b |-- !!(b = a) && (|==> my_half g Tsh a' * public_half g a')%I.
Proof.
  intros.
  iIntros "H".
  iPoseProof (ref_sub(P := P) with "H") as "%".
  rewrite eq_dec_refl in H; subst.
  iSplit; auto.
  rewrite !ghost_part_ref_join.
  iApply (ref_update(P := P)); eauto.
Qed.

Lemma public_part_update : forall g sh (a b a' b' : G) (Ha' : forall c, sepalg.join a c b -> sepalg.join a' c b' /\ (a = b -> a' = b')),
  my_half g sh a * public_half g b |-- !!(if eq_dec sh Tsh then a = b else exists x, sepalg.join a x b) && (|==> my_half g sh a' * public_half g b')%I.
Proof.
  intros.
  iIntros "H".
  iSplit; [iApply (ref_sub with "H")|].
  rewrite !ghost_part_ref_join.
  iApply (part_ref_update(P := P) with "H"); auto.
Qed.

Definition sync_inv g sh R := EX a : G, R g a * my_half g sh a.

Lemma sync_inv_exclusive : forall g sh (R : gname -> G -> mpred), exclusive_mpred (sync_inv g sh R).
Proof.
  intros; unfold exclusive_mpred, sync_inv.
  iIntros "[g1 g2]".
  iDestruct "g1" as (a1) "[? g1]".
  iDestruct "g2" as (a2) "[? g2]".
  iPoseProof (own_valid_2(RA := ref_PCM P) with "[$g1 $g2]") as "%".
  hnf in H.
  destruct H as ((b, ?) & J & _).
  inv J; simpl in *.
  destruct b as [[]|]; auto.
  destruct H as (? & ? & J & ?).
  pose proof (join_self' J); subst.
  contradiction H; apply share_self_join_bot; auto.
Qed.

Lemma sync_commit_simple : forall {inv_names : invG} Ei Eo (Q : mpred) g (x0 x' : G),
  (atomic_shift(B := unit) (fun x => public_half g x) Ei Eo (fun x _ => !!(x = x0) && public_half g x') (fun _ => Q) * my_half g Tsh x0 |-- |==> Q * my_half g Tsh x')%I.
Proof.
  intros; eapply derives_trans; [apply atomic_commit with (R' := fun _ => my_half g Tsh x')|].
  - intros.
    eapply derives_trans; [apply public_update|].
    Intros; apply bupd_mono.
    iIntros "[$ ?]".
    iExists tt; iSplit; auto.
  - apply ghost_seplog.bupd_mono.
    iIntros "Q"; iDestruct "Q" as (_) "$".
Qed.

Lemma sync_rollback : forall {A B} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R' g sh (x0 : G)
  (Ha : forall x, R * a x |-- (|==> EX x1, public_half g x1 * (!!(if eq_dec sh Tsh then x0 = x1 else exists x, sepalg.join x0 x x1) --> (public_half g x1 -* |==> R' * a x)))%I),
  (atomic_shift a Ei Eo b Q * my_half g sh x0 * R |-- atomic_shift a Ei Eo b Q * my_half g sh x0 * R')%I.
Proof.
  intros; rewrite !sepcon_assoc; apply atomic_rollback.
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iPoseProof (ref_sub with "[$my $public]") as "%"; iFrame "my".
  rewrite bi.sep_comm; iApply ("a'" with "[%]"); auto.
Qed.

Lemma sync_commit_gen : forall {A B} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g sh (x0 : G)
  (Ha : forall x, R * a x |-- (|==> EX x1, public_half g x1 * (!!(if eq_dec sh Tsh then x0 = x1 else exists x, sepalg.join x0 x x1) -->
    |==> (EX x0' x1' : G, !!(forall b, sepalg.join x0 b x1 -> sepalg.join x0' b x1' /\ (x0 = x1 -> x0' = x1')) && (my_half g sh x0' * public_half g x1' -* |==> (EX y, b x y * R' y))))%I)%I),
  (atomic_shift a Ei Eo b Q * my_half g sh x0 * R |-- |==> EX y, Q y * R' y)%I.
Proof.
  intros; rewrite sepcon_assoc.
  apply @atomic_commit with (R' := fun y => R' y).
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iPoseProof (ref_sub(P := P) with "[$my $public]") as "%".
  iMod ("a'" with "[%]") as (x0' x1') "[% H]"; first done.
  iDestruct (public_part_update with "[$my $public]") as "[% >[my public]]"; eauto.
  iApply ("H" with "[$my $public]").
Qed.

Lemma sync_commit_same : forall {A B} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g sh (x0 : G)
  (Ha : forall x, R * a x |-- (|==> EX x1, public_half g x1 * (!!(if eq_dec sh Tsh then x0 = x1 else exists x, sepalg.join x0 x x1) -->
    |==> (my_half g sh x0 * public_half g x1 -* |==> (EX y, b x y * R' y)))%I)%I),
  (atomic_shift a Ei Eo b Q * my_half g sh x0 * R |-- |==> EX y, Q y * R' y)%I.
Proof.
  intros; rewrite sepcon_assoc.
  apply @atomic_commit with (R' := fun y => R' y).
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iPoseProof (ref_sub(P := P) with "[$my $public]") as "%".
  iMod ("a'" with "[%]") as "H"; first done.
  iApply "H"; iFrame.
Qed.

Lemma sync_commit_gen1 : forall {A B} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g sh (x0 : G)
  (Ha : forall x, R * a x |-- (|==> EX x1, public_half g x1 * (!!(if eq_dec sh Tsh then x0 = x1 else exists x, sepalg.join x0 x x1) -->
    |==> (EX x0' x1' : G, !!(forall b, sepalg.join x0 b x1 -> sepalg.join x0' b x1' /\ (x0 = x1 -> x0' = x1')) && (my_half g sh x0' * public_half g x1' -* |==> (EX y, b x y) * R')))%I)%I),
  (atomic_shift a Ei Eo b (fun _ => Q) * my_half g sh x0 * R |-- |==> Q * R')%I.
Proof.
  intros; rewrite sepcon_assoc; eapply derives_trans; [apply @atomic_commit with
      (R' := fun _ => R')|].
  - intros; iIntros "((my & R) & a)".
    iMod (Ha with "[$]") as (?) "[public a']".
    iPoseProof (ref_sub(P := P) with "[$my $public]") as "%".
    iMod ("a'" with "[%]") as (x0' x1') "[% H]"; first done.
    iDestruct (public_part_update with "[$my $public]") as "[% >[my public]]"; eauto.
    rewrite exp_sepcon1; iApply ("H" with "[$my $public]").
  - iApply bupd_mono.
    iIntros "Q"; iDestruct "Q" as (?) "[$ $]".
Qed.

Lemma sync_commit_same1 : forall {A B} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g sh (x0 : G)
  (Ha : forall x, R * a x |-- (|==> EX x1, public_half g x1 * (!!(if eq_dec sh Tsh then x0 = x1 else exists x, sepalg.join x0 x x1) -->
    |==> (my_half g sh x0 * public_half g x1 -* |==> (EX y, b x y * R')))%I)%I),
  (atomic_shift a Ei Eo b (fun _ => Q) * my_half g sh x0 * R |-- |==> Q * R')%I.
Proof.
  intros; rewrite sepcon_assoc; eapply derives_trans; [apply @atomic_commit with
      (R' := fun _ => R')|].
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iPoseProof (ref_sub(P := P) with "[$my $public]") as "%".
  iMod ("a'" with "[%]") as "H"; first done.
  iApply "H"; iFrame.
  { iApply bupd_mono.
    iIntros "Q"; iDestruct "Q" as (?) "[$ $]". }
Qed.

(* These are useful when the shared resource matches the lock invariant exactly. *)
Lemma sync_commit1 : forall {inv_names : invG} Ei Eo (b : G -> unit -> mpred) Q g (x0 x' : G)
  (Hb : public_half g x' |-- (|==> b x0 tt)%I),
  (atomic_shift (fun x => public_half g x) Ei Eo b (fun _ => Q) * my_half g Tsh x0 |-- |==> Q * my_half g Tsh x')%I.
Proof.
  intros; eapply derives_trans, sync_commit_simple.
  apply sepcon_derives, derives_refl.
  apply atomic_shift_derives_simple; intros; try solve [by iIntros].
  destruct y.
  iIntros "[% H]"; subst; iMod (Hb with "H"); auto.
Qed.

Lemma sync_commit2 : forall {inv_names : invG} Ei Eo (b : G -> G -> mpred) Q g (x0 x' : G)
  (Hb : public_half g x' |-- (|==> b x0 x0)%I),
  (atomic_shift (fun x => public_half g x) Ei Eo b Q * my_half g Tsh x0 |-- |==> Q x0 * my_half g Tsh x')%I.
Proof.
  intros; eapply derives_trans, sync_commit_simple.
  apply sepcon_derives, derives_refl.
  apply atomic_shift_derives; intros.
  iIntros "a".
  iExists x; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "g"; auto.
  - iIntros (_) "[% g]"; subst.
    iMod (Hb with "[$g]") as "b".
    iExists x0; iFrame.
    iIntros "!> ?"; auto.
Qed.

(* sync_commit for holding two locks simultaneously *)
Lemma two_sync_commit : forall {A B} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g1 g2 sh1 sh2 (x1 x2 : G)
  (Ha : forall x, R * a x |-- (|==> EX y1 y2, public_half g1 y1 * public_half g2 y2 *
    (!!((if eq_dec sh1 Tsh then x1 = y1 else exists z, sepalg.join x1 z y1) /\ (if eq_dec sh2 Tsh then x2 = y2 else exists z, sepalg.join x2 z y2)) -->
    |==> (EX x1' x2' y1' y2' : G, !!((forall z, sepalg.join x1 z y1 -> sepalg.join x1' z y1' /\ (x1 = y1 -> x1' = y1')) /\ (forall z, sepalg.join x2 z y2 -> sepalg.join x2' z y2' /\ (x2 = y2 -> x2' = y2'))) &&
      (my_half g1 sh1 x1' * public_half g1 y1' * my_half g2 sh2 x2' * public_half g2 y2' -* |==> (EX y, b x y * R' y))))%I)%I),
  (atomic_shift a Ei Eo b Q * my_half g1 sh1 x1 * my_half g2 sh2 x2 * R |-- |==> EX y, Q y * R' y)%I.
Proof.
  intros; rewrite -> 2sepcon_assoc.
  apply @atomic_commit with (R' := fun y => R' y).
  intros; iIntros "((my1 & my2 & R) & a)".
  iMod (Ha with "[$]") as (??) "((public1 & public2) &  a')".
  iPoseProof (ref_sub(P := P) with "[$my1 $public1]") as "%".
  iPoseProof (ref_sub(P := P) with "[$my2 $public2]") as "%".
  iMod ("a'" with "[%]") as (????) "[Hsub H]"; first done.
  iDestruct "Hsub" as %[? ?].
  iDestruct (public_part_update with "[$my1 $public1]") as "[% >[my1 public1]]"; eauto.
  iDestruct (public_part_update with "[$my2 $public2]") as "[% >[my2 public2]]"; eauto.
  iApply "H"; iFrame.
Qed.

Lemma two_sync_commit1 : forall {A B} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g1 g2 sh1 sh2 (x1 x2 : G)
  (Ha : forall x, R * a x |-- (|==> EX y1 y2, public_half g1 y1 * public_half g2 y2 *
    (!!((if eq_dec sh1 Tsh then x1 = y1 else exists z, sepalg.join x1 z y1) /\ (if eq_dec sh2 Tsh then x2 = y2 else exists z, sepalg.join x2 z y2)) -->
    |==> (EX x1' x2' y1' y2' : G, !!((forall z, sepalg.join x1 z y1 -> sepalg.join x1' z y1' /\ (x1 = y1 -> x1' = y1')) /\ (forall z, sepalg.join x2 z y2 -> sepalg.join x2' z y2' /\ (x2 = y2 -> x2' = y2'))) &&
      (my_half g1 sh1 x1' * public_half g1 y1' * my_half g2 sh2 x2' * public_half g2 y2' -* |==> ((EX y, b x y) * R'))))%I)%I),
  (atomic_shift a Ei Eo b (fun _ => Q) * my_half g1 sh1 x1 * my_half g2 sh2 x2 * R |-- |==> Q * R')%I.
Proof.
  intros; rewrite -> 2sepcon_assoc.
  eapply derives_trans; [apply @atomic_commit with (R' := fun _ => R')|].
  intros; iIntros "((my1 & my2 & R) & a)".
  iMod (Ha with "[$]") as (??) "((public1 & public2) &  a')".
  iPoseProof (ref_sub(P := P) with "[$my1 $public1]") as "%".
  iPoseProof (ref_sub(P := P) with "[$my2 $public2]") as "%".
  iMod ("a'" with "[%]") as (????) "[Hsub H]"; first done.
  iDestruct "Hsub" as %[? ?].
  iDestruct (public_part_update with "[$my1 $public1]") as "[% >[my1 public1]]"; eauto.
  iDestruct (public_part_update with "[$my2 $public2]") as "[% >[my2 public2]]"; eauto.
  rewrite -exp_sepcon1.
  iApply "H"; iFrame.
  { iApply bupd_mono.
    iIntros "Q"; iDestruct "Q" as (?) "[$ $]". }
Qed.

End locks.

#[export] Hint Resolve sync_inv_exclusive : exclusive.
