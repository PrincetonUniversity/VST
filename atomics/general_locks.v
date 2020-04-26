(* Specifications for locks for use with general invariants, in the style of TaDA *)
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Export VST.progs.invariants.
Require Export VST.progs.fupd.
Require Export VST.atomics.general_atomics.

Section locks.

Context {CS : compspecs}.

(* Should this be generalized to any arbitrary PCM, or maybe just a non-discrete part-ref? *)
Definition my_half {A} g (a : A) := ghost_part(P := discrete_PCM A) Tsh a g.
Definition public_half {A} g (a : A) := ghost_reference(P := discrete_PCM A) a g.
Definition both_halves {A} (a : A) g := ghost_part_ref(P := discrete_PCM A) Tsh a a g.

Lemma both_halves_join : forall {A} g (a : A), my_half g a * public_half g a = both_halves a g.
Proof.
  intros.
  apply (ghost_part_ref_join(P := discrete_PCM A)).
Qed.

Lemma public_agree : forall {A} g (a b: A),
    my_half g a * public_half g b |-- !!(a = b).
Proof.
  intros. unfold my_half, public_half. sep_apply (ref_sub (P := discrete_PCM A)).
  rewrite if_true; auto. entailer!.
Qed.

Lemma public_update : forall {A} g (a b a' : A),
  (my_half g a * public_half g b |-- !!(b = a) && |==> my_half g a' * public_half g a')%I.
Proof.
  intros.
  iIntros "H".
  iPoseProof (ref_sub(P := discrete_PCM A) with "H") as "%".
  rewrite eq_dec_refl in H; subst.
  iSplit; auto.
  rewrite !ghost_part_ref_join.
  iApply (ref_update(P := discrete_PCM A)); eauto.
Qed.

Definition sync_inv {A} g R := EX a : A, R g a * my_half g a.

Lemma sync_inv_exclusive : forall {A} g (R : gname -> A -> mpred), exclusive_mpred (sync_inv g R).
Proof.
  intros; unfold exclusive_mpred, sync_inv.
  iIntros "[g1 g2]".
  iDestruct "g1" as (a1) "[? g1]".
  iDestruct "g2" as (a2) "[? g2]".
  iPoseProof (own_valid_2(RA := ref_PCM (discrete_PCM _)) with "[$g1 $g2]") as "%".
  hnf in H.
  destruct H as ((b, ?) & J & _).
  inv J; simpl in *.
  destruct b as [[]|]; auto.
  destruct H as (? & ? & J & ?).
  apply join_Tsh in J as []; contradiction.
Qed.

Lemma sync_commit_simple : forall {A} {inv_names : invG} Ei Eo (Q : mpred) g (x0 x' : A),
  (atomic_shift(B := unit) (fun x => public_half g x) Ei Eo (fun x _ => !!(x = x0) && public_half g x') (fun _ => Q) * my_half g x0 |-- |==> Q * my_half g x')%I.
Proof.
  intros; eapply derives_trans; [apply atomic_commit with (R' := fun _ => my_half g x')|].
  - intros.
    eapply derives_trans; [apply public_update|].
    Intros; apply bupd_mono.
    iIntros "[$ ?]".
    iExists tt; iSplit; auto.
  - apply bupd_mono.
    iIntros "Q"; iDestruct "Q" as (_) "$".
Qed.

Lemma sync_rollback : forall {A B C} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R' g (x0 : C)
  (Ha : (forall x, R * a x |-- |==> EX x1, public_half g x1 * (!!(x1 = x0) --> (public_half g x0 -* |==> R' * a x)))%I),
  (atomic_shift a Ei Eo b Q * my_half g x0 * R |-- atomic_shift a Ei Eo b Q * my_half g x0 * R')%I.
Proof.
  intros; rewrite !sepcon_assoc; apply atomic_rollback.
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iDestruct (public_update with "[$my $public]") as "[% >[$ public]]"; subst.
  rewrite bi.sep_comm; iApply ("a'" with "[%]"); auto.
Qed.

Lemma sync_commit_gen : forall {A B C} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g (x0 : C)
  (Ha : (forall x, R * a x |-- |==> EX x1, public_half g x1 * (!!(x1 = x0) --> |==> (EX x' : C, my_half g x' * public_half g x' -* |==> (EX y, b x y * R' y)))%I)%I),
  (atomic_shift a Ei Eo b Q * my_half g x0 * R |-- |==> EX y, Q y * R' y)%I.
Proof.
  intros; rewrite sepcon_assoc.
  apply atomic_commit with (R'0 := fun y => R' y).
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iPoseProof (ref_sub(P := discrete_PCM C) with "[$my $public]") as "%".
  rewrite eq_dec_refl in H0; subst.
  iMod ("a'" with "[%]") as (x') "H"; first done.
  iDestruct (public_update with "[$my $public]") as "[% >[my public]]"; subst.
  iApply ("H" with "[$my $public]").
Qed.

Lemma sync_commit_gen1 : forall {A B C} {inv_names : invG} a Ei Eo (b : A -> B -> mpred) Q R R' g (x0 : C)
  (Ha : (forall x, R * a x |-- |==> EX x1, public_half g x1 * (!!(x1 = x0) --> |==> (EX x' : C, my_half g x' * public_half g x' -* |==> (EX y, b x y) * R')%I))%I),
  (atomic_shift a Ei Eo b (fun _ => Q) * my_half g x0 * R |-- |==> Q * R')%I.
Proof.
  intros; rewrite sepcon_assoc; eapply derives_trans; [apply atomic_commit with (R'0 := fun _ => R')|].
  - intros; iIntros "((my & R) & a)".
    iMod (Ha with "[$]") as (?) "[public a']".
    iPoseProof (ref_sub(P := discrete_PCM C) with "[$my $public]") as "%".
    rewrite eq_dec_refl in H0; subst.
    iDestruct ("a'" with "[%]") as (x') "H"; first done.
    iDestruct (public_update with "[$my $public]") as "[% >[my public]]"; subst.
    rewrite exp_sepcon1; iApply ("H" with "[$my $public]").
  - iApply bupd_mono.
    iIntros "Q"; iDestruct "Q" as (?) "[$ $]".
Qed.

(* These are useful when the shared resource matches the lock invariant exactly. *)
Lemma sync_commit1 : forall {A} {inv_names : invG} Ei Eo (b : A -> unit -> mpred) Q g (x0 x' : A)
  (Hb : (public_half g x' |-- |==> b x0 tt)%I),
  (atomic_shift (fun x => public_half g x) Ei Eo b (fun _ => Q) * my_half g x0 |-- |==> Q * my_half g x')%I.
Proof.
  intros; eapply derives_trans, sync_commit_simple.
  apply sepcon_derives, derives_refl.
  apply atomic_shift_derives_simple; intros; try solve [by iIntros].
  destruct y.
  iIntros "[% H]"; subst; iMod (Hb with "H"); auto.
Qed.

Lemma sync_commit2 : forall {A} {inv_names : invG} Ei Eo (b : A -> A -> mpred) Q g (x0 x' : A)
  (Hb : (public_half g x' |-- |==> b x0 x0)%I),
  (atomic_shift (fun x => public_half g x) Ei Eo b Q * my_half g x0 |-- |==> Q x0 * my_half g x')%I.
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

End locks.

Hint Resolve sync_inv_exclusive : exclusive.
