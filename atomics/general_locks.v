(* Specifications for locks for use with general invariants, in the style of the atomic syncer *)
From VST.concurrency Require Import conclib lock_specs.
From VST.atomics Require Export general_atomics.
From iris_ora.algebra Require Import frac_auth.

Section locks.

Context {A : cmra}.

Context `{!inG Σ (frac_authR A)}.

Definition my_half g sh (a : A) := own g (frac_auth_frag(A := A) sh a : frac_authR A).
Definition public_half g (a : A) := own g (frac_auth_auth(A := A) a : frac_authR A).
Definition both_halves (a : A) g := own g (frac_auth_auth(A := A) a ⋅ frac_auth_frag(A := A) 1 a : frac_authR A).

Lemma my_half_join : forall sh1 sh2 a1 a2 g,
  my_half g sh1 a1 ∗ my_half g sh2 a2 ⊣⊢ my_half g (sh1 ⋅ sh2) (a1 ⋅ a2).
Proof.
  intros; rewrite /my_half -own_op //.
Qed.

Lemma both_halves_join : forall g (a : A), my_half g 1 a ∗ public_half g a ⊣⊢ both_halves a g.
Proof.
  intros; rewrite /my_half /public_half -own_op //.
Qed.

Lemma public_agree : forall g (a b: A), my_half g 1 a ∗ public_half g b ⊢ a ≡ b.
Proof.
  intros.
  iIntros "(a & b)"; iPoseProof (own_valid_2 with "a b") as "H".
  rewrite frac_auth_agree_fullI internal_eq_sym //.
Qed.

Lemma public_part_agree : forall g sh (a b: A), my_half g sh a ∗ public_half g b ⊢ if decide (sh = 1%Qp) then a ≡ b else ∃ c, b ≡ a ⋅ c.
Proof.
  intros.
  iIntros "(a & b)"; iPoseProof (own_valid_2 with "a b") as "H".
  rewrite frac_auth_agreeI; if_tac; try done.
  rewrite internal_eq_sym //.
Qed.

Lemma public_update : forall g (a b a' : A), ✓ a' ->
  my_half g 1 a ∗ public_half g b ⊢ b ≡ a ∧ (|==> my_half g 1 a' ∗ public_half g a')%I.
Proof.
  intros.
  iIntros "H".
  iSplit. { by iApply internal_eq_sym; iApply public_agree. }
  rewrite !(bi.sep_comm (my_half _ _ _)).
  rewrite /my_half /public_half -!own_op.
  iApply (own_update with "H").
  by apply @frac_auth_update_1.
Qed.

Lemma public_part_update : forall g sh (a b a' b' : A) (Ha' : local_update(A := A) (b, a) (b', a')),
  my_half g sh a ∗ public_half g b ⊢ (if decide (sh = 1%Qp) then a ≡ b else ∃ c, b ≡ a ⋅ c) ∧ (|==> my_half g sh a' ∗ public_half g b')%I.
Proof.
  intros.
  iIntros "H".
  iSplit.
  - by iApply public_part_agree.
  - rewrite /my_half /public_half -!own_op.
    iApply (own_update with "H").
    by apply @frac_auth_update.
Qed.

(*(* lock_inv with share implies TaDA lock specs with share *)
Context {LI : lock_impl}.

Definition lock_state g (b : bool) := ghost_var (if b then 1 else gsh2) tt g.
Definition lock_ref sh p g := lock_inv sh p (ghost_var gsh1 tt g).

  Program Definition release_spec :=
    ATOMIC TYPE (rmaps.ConstType _) INVS empty
    WITH sh, p, g
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of p)
       SEP (lock_ref sh p g) | (lock_state g true)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_ref sh p g) | (lock_state g false).

  Program Definition acquire_spec :=
    ATOMIC TYPE (rmaps.ConstType _) OBJ l INVS empty
    WITH sh, p, g
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of p)
       SEP (lock_ref sh p g) | (lock_state g l)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_ref sh p g) | (⌜l = false⌝ ∧ lock_state g true).
(* it's inelegant but seems inevitable that we need the lock_inv locally here. This seems
   to be a consequence of baking share ownership into the lock_inv assertion. *)

Lemma acquire_tada : funspec_sub lock_specs.acquire_spec acquire_spec.
Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in ∗. Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". destruct x2 as (((sh, h), g), Q).
    set (AS := atomic_shift _ _ _ _ _). iExists nil, (sh, h, ghost_var gsh1 tt g), AS.
    iSplit.
    - unfold PROPx, PARAMSx, ALOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
      iDestruct "H" as "(% & % & % & $ & $ & _)"; auto.
    - iPureIntro. intros. Intros. (* need fupd in postcondition *)
Admitted.

Lemma release_tada : funspec_sub lock_specs.release_spec release_spec.
Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in ∗. Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H". destruct x2 as (((sh, h), g), Q).
    unfold PROPx, PARAMSx, ALOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
    iDestruct "H" as "([% _] & % & % & AS & l & _)".
    iMod "AS" as (_) "[lock Hclose]".
    unfold lock_state at 1.
    erewrite <- ghost_var_share_join; try apply gsh1_gsh2_join; auto.
    iDestruct "lock" as "[g1 g2]"; iDestruct "Hclose" as "[_ Hclose]".
    iMod ("Hclose" $! tt with "[$g2]") as "Q".
    iExists nil, (sh, h, ghost_var gsh1 tt g, ghost_var gsh1 tt g, lock_ref sh h g), Q.
    iModIntro; iSplit.
    - iFrame; do 2 (iSplit; [auto|]).
      iSplitL ""; [|iSplit; [|iSplit]; auto; iIntros "$"].
      iApply exclusive_weak_exclusive; auto.
      unfold exclusive_mpred.
      rewrite ghost_var_share_join_gen; Intros sh'.
      apply join_self, identity_share_bot in H4; contradiction.
    - iPureIntro. intros. entailer!.
Qed.*)


Definition sync_inv g sh R := ∃ a : A, R g a ∗ my_half g sh a.

(*Lemma sync_inv_exclusive : forall g sh (R : gname -> A -> mpred), exclusive_mpred (sync_inv g sh R).
Proof.
  intros; unfold exclusive_mpred, sync_inv.
  iIntros "[g1 g2]".
  iDestruct "g1" as (a1) "[? g1]".
  iDestruct "g2" as (a2) "[? g2]".
  iPoseProof (own_valid_2(RA := ref_PCM P) with "[$g1 $g2]") as "%".
  hnf in H.
  destruct H as ((b, ?) & J & _).
  inv J; simpl in ∗.
  destruct b as [[]|]; auto.
  destruct H as (? & ? & J & ?).
  pose proof (join_self' J); subst.
  contradiction H; apply share_self_join_bot; auto.
Qed.*)

Context `{!heapGS Σ}.

Lemma sync_commit_simple : forall Eo Ei (Q : mpred) g (x0 x' : A), ✓ x' ->
  (atomic_shift(B := unit) (fun x => public_half g x) Eo Ei (fun x _ => x ≡ x0 ∧ public_half g x') (fun _ => Q) ∗ my_half g 1 x0 ⊢ |={Eo}=> Q ∗ my_half g 1 x')%I.
Proof.
  intros.
  rewrite atomic_commit_fupd.
  - iIntros ">(% & $ & H) !>".
    iApply "H".
  - intros; rewrite public_update //.
    by iIntros "($ & >($ & $))".
Qed.

#[global] Instance sub_persistent sh (a b : A) : Persistent (if decide (sh = 1%Qp) then a ≡ b else ∃ c, b ≡ a ⋅ c : mpred)%I.
Proof.
  if_tac; apply _.
Qed.

Lemma sync_rollback : forall {A0 B} a Eo Ei (b : A0 -> B -> mpred) (Q : B -> mpred) R R' g sh (x0 : A)
  (Ha : forall x, R ∗ a x ⊢ (|==> ∃ x1, public_half g x1 ∗ (<affine> (if decide (sh = 1%Qp) then x0 ≡ x1 else ∃ x, x1 ≡ x0 ⋅ x) -∗ (public_half g x1 -∗ |==> R' ∗ a x))%I)),
  (atomic_shift a Eo Ei b Q ∗ my_half g sh x0 ∗ R ⊢ |={Eo}=> atomic_shift a Eo Ei b Q ∗ my_half g sh x0 ∗ R')%I.
Proof.
  intros; apply atomic_rollback_fupd.
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iDestruct (public_part_agree with "[$my $public]") as "#sub"; iFrame "my".
  rewrite bi.sep_comm; iApply ("a'" with "sub"); auto.
Qed.

Lemma sync_commit_gen : forall {A0 B} a Eo Ei (b : A0 -> B -> mpred) Q R R' g sh (x0 : A)
  (Ha : forall x, R ∗ a x ⊢ (|==> ∃ x1, public_half g x1 ∗ (<affine> (if decide (sh = 1%Qp) then x0 ≡ x1 else ∃ x, x1 ≡ x0 ⋅ x) -∗
    |==> (∃ x0' x1' : A, ⌜local_update(A := A) (x1, x0) (x1', x0')⌝ ∧ (my_half g sh x0' ∗ public_half g x1' -∗ |==> (∃ y, b x y ∗ R' y))))%I)%I),
  (atomic_shift a Eo Ei b Q ∗ my_half g sh x0 ∗ R ⊢ |={Eo}=> ∃ y, Q y ∗ R' y)%I.
Proof.
  intros.
  apply @atomic_commit_fupd with (R' := fun y => R' y).
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iDestruct (public_part_agree with "[$my $public]") as "#sub".
  iMod ("a'" with "sub") as (x0' x1') "[% H]".
  iDestruct (public_part_update with "[$my $public]") as "[#? >[my public]]"; eauto.
  iApply ("H" with "[$my $public]").
Qed.

Lemma sync_commit_same : forall {A0 B} a Eo Ei (b : A0 -> B -> mpred) Q R R' g sh (x0 : A)
  (Ha : forall x, R ∗ a x ⊢ (|==> ∃ x1, public_half g x1 ∗ (<affine> (if decide (sh = 1%Qp) then x0 ≡ x1 else ∃ x, x1 ≡ x0 ⋅ x) -∗
    |==> (my_half g sh x0 ∗ public_half g x1 -∗ |==> (∃ y, b x y ∗ R' y)))%I)%I),
  (atomic_shift a Eo Ei b Q ∗ my_half g sh x0 ∗ R ⊢ |={Eo}=> ∃ y, Q y ∗ R' y)%I.
Proof.
  intros.
  apply @atomic_commit_fupd with (R' := fun y => R' y).
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iDestruct (public_part_agree with "[$my $public]") as "#sub".
  iMod ("a'" with "sub") as "H".
  iApply "H"; iFrame.
Qed.

Lemma sync_commit_gen1 : forall {A0 B} a Eo Ei (b : A0 -> B -> mpred) Q R R' g sh (x0 : A)
  (Ha : forall x, R ∗ a x ⊢ (|==> ∃ x1, public_half g x1 ∗ (<affine> (if decide (sh = 1%Qp) then x0 ≡ x1 else ∃ x, x1 ≡ x0 ⋅ x) -∗
    |==> (∃ x0' x1' : A, ⌜local_update(A := A) (x1, x0) (x1', x0')⌝ ∧ (my_half g sh x0' ∗ public_half g x1' -∗ |==> (∃ y, b x y) ∗ R')))%I)%I),
  (atomic_shift a Eo Ei b (fun _ => Q) ∗ my_half g sh x0 ∗ R ⊢ |={Eo}=> Q ∗ R')%I.
Proof.
  intros.
  rewrite (atomic_commit_fupd _ _ _ _ _ _ (fun _ => R')).
  - iIntros ">Q !>"; iDestruct "Q" as (?) "[$ $]".
  - intros; iIntros "((my & R) & a)".
    iMod (Ha with "[$]") as (?) "[public a']".
    iDestruct (public_part_agree with "[$my $public]") as "#sub".
    iMod ("a'" with "sub") as (x0' x1') "[% H]".
    iDestruct (public_part_update with "[$my $public]") as "[#? >[my public]]"; eauto.
    rewrite -bi.sep_exist_r; iApply ("H" with "[$my $public]").
Qed.

Lemma sync_commit_same1 : forall {A0 B} a Eo Ei (b : A0 -> B -> mpred) Q R R' g sh (x0 : A)
  (Ha : forall x, R ∗ a x ⊢ (|==> ∃ x1, public_half g x1 ∗ (<affine> (if decide (sh = 1%Qp) then x0 ≡ x1 else ∃ x, x1 ≡ x0 ⋅ x) -∗
    |==> (my_half g sh x0 ∗ public_half g x1 -∗ |==> (∃ y, b x y ∗ R')))%I)%I),
  (atomic_shift a Eo Ei b (fun _ => Q) ∗ my_half g sh x0 ∗ R ⊢ |={Eo}=> Q ∗ R')%I.
Proof.
  intros.
  rewrite (atomic_commit_fupd _ _ _ _ _ _ (fun _ => R')).
  { iIntros ">Q !>"; iDestruct "Q" as (?) "[$ $]". }
  intros; iIntros "((my & R) & a)".
  iMod (Ha with "[$]") as (?) "[public a']".
  iDestruct (public_part_agree with "[$my $public]") as "#sub".
  iMod ("a'" with "sub") as "H".
  iApply "H"; iFrame.
Qed.

(* These are useful when the shared resource matches the lock invariant exactly. *)
Lemma sync_commit1 : forall Eo Ei (b : A -n> unit -d> mpred) Q g (x0 x' : A) (Hx' : ✓ x')
  (Hb : public_half g x' ⊢ (|==> b x0 tt)%I),
  (atomic_shift (fun x => public_half g x) Eo Ei b (fun _ => Q) ∗ my_half g 1 x0 ⊢ |={Eo}=> Q ∗ my_half g 1 x')%I.
Proof.
  intros; rewrite -sync_commit_simple //.
  iIntros "(A & $)".
  iApply (atomic_shift_derives_simple with "A"); try solve [by iIntros].
  destruct y.
  iIntros "[Heq H]".
  iMod (Hb with "H") as "Hb".
  iIntros "!>"; iStopProof.
  rewrite -bi.persistent_and_affinely_sep_l internal_eq_sym; rewrite -> (internal_eq_rewrite _ _ (fun a => b a ())).
  apply bi.impl_elim_l.
  { intros ? x1 x2 Hdist. assert (b x1 ≡{n}≡ b x2) by rewrite Hdist //; auto. }
Qed.

Lemma sync_commit2 : forall Eo Ei (b : A -n> A -d> mpred) Q g (x0 x' : A) (Hx' : ✓ x')
  (Hb : public_half g x' ⊢ (|==> b x0 x0)%I),
  (atomic_shift (fun x => public_half g x) Eo Ei b Q ∗ my_half g 1 x0 ⊢ |={Eo}=> Q x0 ∗ my_half g 1 x')%I.
Proof.
  intros; rewrite -sync_commit_simple //.
  iIntros "(A & $)".
  iApply (atomic_shift_derives with "A"); intros.
  iIntros "a".
  iExists x; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "g"; auto.
  - iIntros (_) "[Heq g]".
    iMod (Hb with "[$g]") as "b".
    iExists x0; iFrame.
    iIntros "!>"; iSplitR ""; last by auto.
    iStopProof.
    rewrite -bi.persistent_and_affinely_sep_l internal_eq_sym; rewrite -> (internal_eq_rewrite _ _ (fun a => b a x0)).
    apply bi.impl_elim_l.
    { intros ? x1 x2 Hdist. assert (b x1 ≡{n}≡ b x2) by rewrite Hdist //; auto. }
Qed.

(* sync_commit for holding two locks simultaneously *)
Lemma two_sync_commit : forall {A0 B} a Eo Ei (b : A0 -> B -> mpred) Q R R' g1 g2 sh1 sh2 (x1 x2 : A)
  (Ha : forall x, R ∗ a x ⊢ (|==> ∃ y1 y2, public_half g1 y1 ∗ public_half g2 y2 ∗
    (<affine> (if decide (sh1 = 1%Qp) then x1 ≡ y1 else ∃ x, y1 ≡ x1 ⋅ x) -∗ (if decide (sh2 = 1%Qp) then x2 ≡ y2 else ∃ x, y2 ≡ x2 ⋅ x) -∗
    |==> (∃ x1' x2' y1' y2' : A, ⌜local_update(A := A) (y1, x1) (y1', x1') /\ local_update(A := A) (y2, x2) (y2', x2')⌝ ∧
      (my_half g1 sh1 x1' ∗ public_half g1 y1' ∗ my_half g2 sh2 x2' ∗ public_half g2 y2' -∗ |==> (∃ y, b x y ∗ R' y))))%I)%I),
  (atomic_shift a Eo Ei b Q ∗ my_half g1 sh1 x1 ∗ my_half g2 sh2 x2 ∗ R ⊢ |={Eo}=> ∃ y, Q y ∗ R' y)%I.
Proof.
  intros.
  apply @atomic_commit_fupd with (R' := fun y => R' y).
  intros; iIntros "((my1 & my2 & R) & a)".
  iMod (Ha with "[$]") as (??) "(public1 & public2 & a')".
  iDestruct (public_part_agree with "[$my1 $public1]") as "#sub1".
  iDestruct (public_part_agree with "[$my2 $public2]") as "#sub2".
  iMod ("a'" with "sub1 sub2") as (????) "[(% & %) H]".
  iDestruct (public_part_update with "[$my1 $public1]") as "[? >[my1 public1]]"; eauto.
  iDestruct (public_part_update with "[$my2 $public2]") as "[? >[my2 public2]]"; eauto.
  iApply "H"; iFrame.
Qed.

Lemma two_sync_commit1 : forall {A0 B} a Eo Ei (b : A0 -> B -> mpred) Q R R' g1 g2 sh1 sh2 (x1 x2 : A)
  (Ha : forall x, R ∗ a x ⊢ (|==> ∃ y1 y2, public_half g1 y1 ∗ public_half g2 y2 ∗
    (<affine> (if decide (sh1 = 1%Qp) then x1 ≡ y1 else ∃ x, y1 ≡ x1 ⋅ x) -∗ (if decide (sh2 = 1%Qp) then x2 ≡ y2 else ∃ x, y2 ≡ x2 ⋅ x) -∗
    |==> (∃ x1' x2' y1' y2' : A, ⌜local_update(A := A) (y1, x1) (y1', x1') /\ local_update(A := A) (y2, x2) (y2', x2')⌝ ∧
      (my_half g1 sh1 x1' ∗ public_half g1 y1' ∗ my_half g2 sh2 x2' ∗ public_half g2 y2' -∗ |==> ((∃ y, b x y) ∗ R'))))%I)),
  (atomic_shift a Eo Ei b (fun _ => Q) ∗ my_half g1 sh1 x1 ∗ my_half g2 sh2 x2 ∗ R ⊢ |={Eo}=> Q ∗ R')%I.
Proof.
  intros.
  rewrite (atomic_commit_fupd _ _ _ _ _ _ (fun _ => R')).
  { iIntros ">Q !>"; iDestruct "Q" as (?) "[$ $]". }
  intros; iIntros "((my1 & my2 & R) & a)".
  iMod (Ha with "[$]") as (??) "(public1 & public2 & a')".
  iDestruct (public_part_agree with "[$my1 $public1]") as "#sub1".
  iDestruct (public_part_agree with "[$my2 $public2]") as "#sub2".
  iMod ("a'" with "sub1 sub2") as (????) "[(% & %) H]".
  iDestruct (public_part_update with "[$my1 $public1]") as "[? >[my1 public1]]"; eauto.
  iDestruct (public_part_update with "[$my2 $public2]") as "[? >[my2 public2]]"; eauto.
  rewrite -bi.sep_exist_r.
  iApply "H"; iFrame.
Qed.

End locks.
