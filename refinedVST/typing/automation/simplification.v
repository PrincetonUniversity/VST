(** This file collects simplification instances specific to RefinedCC *)
From VST.lithium Require Import simpl_classes.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Import programs int.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

Global Instance simpl_it_elem_of (z : Z) (it : Ctypes.type) :
  SimplBoth (z ∈ it) (min_int it ≤ z ∧ z ≤ max_int it).
Proof.
  rewrite /elem_of /elem_of_type /in_range.
  split.
  - destruct it; simpl; try done; try destruct i; destruct s; simpl; rep_lia.
  - destruct it; simpl; try lia; try destruct i; destruct s; simpl; rep_lia.
Qed.

(** * layout *)
(* Global Instance simpl_layout_eq ly1 ly2 : SimplAndRel (=) ly1 ly2 (ly1.(ly_size) = ly2.(ly_size) ∧ ly_align ly1 = ly_align ly2).
Proof. split; rewrite -ly_align_log_ly_align_eq_iff; destruct ly1,ly2; naive_solver. Qed.

Global Instance simpl_layout_leq ly1 ly2 : SimplBoth (ly1 ⊑ ly2) (ly1.(ly_size) ≤ ly2.(ly_size) ∧ ly_align ly1 ≤ ly_align ly2)%nat.
Proof. split; rewrite /ly_align -Nat.pow_le_mono_r_iff //; lia. Qed.

Global Instance ly_size_ly_offset_eq ly n m `{!CanSolve (n ≤ ly_size ly)%nat}:
  SimplBothRel (=) (ly_size (ly_offset ly n)) m (ly_size ly = m + n)%nat.
Proof. unfold CanSolve in *. rewrite {1}/ly_size/=. split; lia. Qed.

Global Instance simpl_is_power_of_two_align ly :
  SimplAnd (is_power_of_two (ly_align ly)) (True).
Proof. split => ?; last naive_solver. by eexists _. Qed.

(** * aligned_to *)
Global Instance simpl_aligned_to_add1 l (n : nat) : SimplBoth ((l +ₗ n) `aligned_to` n) (l `aligned_to` n).
Proof. rewrite -{1}(Z.mul_1_l n). apply aligned_to_add. Qed.
Global Instance simpl_aligned_to_add l m (n : nat) : SimplBoth ((l +ₗ m * n) `aligned_to` n) (l `aligned_to` n).
Proof. apply aligned_to_add. Qed.

Global Instance simpl_learn_aligned_to_mult l o n1 n2
  `{!CaesiumConfigEnforceAlignment} `{!CanSolve (l `aligned_to` n2)} `{!CanSolve (0 ≤ o)} :
  SimplImplUnsafe false ((l +ₗ o) `aligned_to` (n1 * n2)) (∃ o' : nat, o = o' * n2) | 100.
Proof.
  unfold CanSolve in *. move => Halign.
  odestruct (aligned_to_mult_eq l n1 n2 o) as [x ?] => //; subst.
  eexists (Z.to_nat x). destruct x; lia.
Qed.

(** * location offset *)
Global Instance simpl_offset_inj l1 l2 sl n : SimplBothRel (=) (l1 at{sl}ₗ n) (l2 at{sl}ₗ n) (l1 = l2).
Proof. unfold GetMemberLoc. split; [apply shift_loc_inj1| naive_solver]. Qed.

Global Instance simpl_shift_loc_eq l n : SimplBothRel (=) l (l +ₗ n) (n = 0).
Proof. split; [by rewrite -{1}(shift_loc_0 l)=> /shift_loc_inj2 | move => ->; by rewrite shift_loc_0 ]. Qed. *)

(** * NULL *)

(* Global Instance simpl_to_NULL_val_of_loc (l : address):
  SimplAndRel (=) NULL (l) (l = NULL_loc).
Proof. split; unfold NULL; naive_solver. Qed. *)

(** * value representation *)
Global Instance simpl_and_eq_val_of_loc l1 l2
  `{!TCDone (match val2adr l1 with | Some _ => True | None => False end)}:
  SimplAnd (val2adr l1 = val2adr l2) (l1 = l2).
Proof.
  destruct l1 eqn:?; try done.
  split; intros.
  -  subst; done.
  - destruct l2 eqn:?; try done.
    inv H. done.
Qed.