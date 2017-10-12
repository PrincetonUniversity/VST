Require Import String Ascii List ZArith.
Import ListNotations.
Require Import VST.floyd.proofauto.

Fixpoint string_to_Z (s : string) :=
  match s with
  | EmptyString => []
  | String a s' => Byte.signed (Byte.repr (Z.of_nat (nat_of_ascii a))) :: string_to_Z s'
  end.

Lemma string_to_Z_app : forall s1 s2, string_to_Z (append s1 s2) = string_to_Z s1 ++ string_to_Z s2.
Proof.
  induction s1; auto; intros; simpl.
  rewrite IHs1; auto.
Qed.

Lemma append_empty : forall s, append s EmptyString = s.
Proof.
  induction s; auto; simpl.
  rewrite IHs; auto.
Qed.

Definition repable_char i := Byte.min_signed <= i <= Byte.max_signed.

Lemma repable_char_0 : repable_char 0.
Proof.
  split.
  - pose proof Byte.min_signed_neg; omega.
  - pose proof Byte.max_signed_pos; omega.
Qed.

Lemma repable_char_int : forall i, repable_char i -> repable_signed i.
Proof.
  unfold repable_char, repable_signed, Byte.min_signed, Byte.max_signed,
    Int.min_signed, Int.max_signed; simpl; intros; omega.
Qed.

Lemma repable_byte : forall a, repable_char (Byte.signed a).
Proof.
  apply Byte.signed_range.
Qed.

Hint Resolve repable_char_0 repable_byte repable_char_int.

Lemma repable_string : forall s, Forall repable_char (string_to_Z s).
Proof.
  induction s; constructor; auto.
Qed.

Lemma repable_string_i : forall s i, repable_char (Znth i (string_to_Z s ++ [0]) 0).
Proof.
  intros.
  destruct (zlt i 0).
  { rewrite Znth_underflow; auto. }
  destruct (zlt i (Zlength (string_to_Z s))).
  { rewrite app_Znth1 by auto.
    apply Forall_Znth, repable_string; omega. }
  rewrite app_Znth2 by auto.
  destruct (eq_dec (i - Zlength (string_to_Z s)) 0).
  { rewrite e, Znth_0_cons; auto. }
  { rewrite Znth_overflow; auto.
    rewrite Zlength_cons, Zlength_nil; omega. }
Qed.

Lemma sign_ext_char : forall c, repable_char c ->
  Int.sign_ext 8 (Int.repr c) = Int.repr c.
Proof.
  intros; apply sign_ext_inrange.
  rewrite Int.signed_repr; auto.
  apply repable_char_int; auto.
Qed.

Opaque N.mul.

Lemma N_of_digits_inj : forall l1 l2, length l1 = length l2 ->
  N_of_digits l1 = N_of_digits l2 -> l1 = l2.
Proof.
  induction l1; destruct l2; auto; try discriminate; simpl; intros.
  rewrite <- N2Z.id in H0.
  rewrite <- (N2Z.id (_ + _)) in H0.
  apply Z2N.inj in H0; try apply N2Z.is_nonneg.
  rewrite !N2Z.inj_add, !N2Z.inj_mul in H0.
  destruct a, b; simpl in *; try (apply f_equal, IHl1; auto; apply N2Z.inj; omega).
  - assert (Z.odd (1 + 2 * Z.of_N (N_of_digits l1)) = true) as Hodd.
    { rewrite Z.odd_add_mul_2; auto. }
    rewrite H0, Z.odd_add_mul_2 in Hodd; discriminate.
  - assert (Z.odd (1 + 2 * Z.of_N (N_of_digits l2)) = true) as Hodd.
    { rewrite Z.odd_add_mul_2; auto. }
    rewrite <- H0, Z.odd_add_mul_2 in Hodd; discriminate.
Qed.

Corollary nat_of_ascii_inj : forall a1 a2, nat_of_ascii a1 = nat_of_ascii a2 -> a1 = a2.
Proof.
  destruct a1 as (?, ?, ?, ?, ?, ?, ?, ?), a2 as (?, ?, ?, ?, ?, ?, ?, ?).
  unfold nat_of_ascii; intro X.
  apply Nnat.N2Nat.inj, N_of_digits_inj in X; auto; congruence.
Qed.

Lemma N_of_digits_range : forall l, 0 <= Z.of_N (N_of_digits l) < 2 ^ (Zlength l).
Proof.
  induction l; simpl; [omega|].
  rewrite Zlength_cons, N2Z.inj_add, N2Z.inj_mul.
  unfold Z.succ; rewrite Z.pow_add_r by (pose proof Zlength_nonneg l; omega); simpl.
  unfold Z.pow_pos; simpl.
  if_tac; simpl; omega.
Qed.

Corollary nat_of_ascii_range : forall a, 0 <= Z.of_nat (nat_of_ascii a) < Byte.modulus.
Proof.
  destruct a.
  unfold nat_of_ascii.
  rewrite N_nat_Z; apply N_of_digits_range.
Qed.

Lemma string_to_Z_inj : forall s1 s2, string_to_Z s1 = string_to_Z s2 -> s1 = s2.
Proof.
  induction s1; destruct s2; auto; try discriminate; simpl; intro X; inv X.
  rewrite !Byte.signed_repr_eq in *.
  erewrite (nat_of_ascii_inj _ a0), IHs1; eauto.
  apply Nat2Z.inj.
  pose proof (nat_of_ascii_range a); pose proof (nat_of_ascii_range a0).
  rewrite !Zmod_small in * by auto.
  destruct (zlt _ _), (zlt _ _); auto; omega.
Qed.

Section CS.
  Context {CS : compspecs}.

Definition cstring s p := let ls := string_to_Z s in
  !!(~In 0 ls) &&
  data_at Tsh (tarray tschar (Zlength ls + 1)) (map Vint (map Int.repr (ls ++ [0]))) p.

Lemma cstring_local_facts: forall s p, cstring s p |-- !! (isptr p).
Proof.
  intros; unfold cstring; entailer!.
Qed.

Hint Resolve cstring_local_facts : saturate_local.

Lemma cstring_valid_pointer: forall s p, cstring s p |-- valid_pointer p.
Proof.
  intros; unfold cstring; Intros.
  apply data_at_valid_ptr; auto.
  unfold tarray; simpl.
  pose proof (Zlength_nonneg (string_to_Z s)).
  rewrite Z.max_r; omega.
Qed.

Hint Resolve cstring_valid_pointer : valid_pointer.

Definition cstringn s n p := let ls := string_to_Z s in
  !!(~In 0 ls) &&
  data_at Tsh (tarray tschar n) (map Vint (map Int.repr (ls ++ [0])) ++
    list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef) p.

Lemma cstringn_equiv : forall s p, cstring s p = cstringn s (Zlength (string_to_Z s) + 1) p.
Proof.
  intros; unfold cstring, cstringn.
  rewrite Zminus_diag, app_nil_r; auto.
Qed.

Lemma cstringn_local_facts: forall s n p, cstringn s n p |-- !! (isptr p /\ Zlength (string_to_Z s) + 1 <= n).
Proof.
  intros; unfold cstringn; entailer!.
  autorewrite with sublist in H1.
  pose proof (Zlength_nonneg (string_to_Z s)).
  pose proof (Zlength_nonneg (list_repeat (Z.to_nat (n - (Zlength (string_to_Z s) + 1))) Vundef)).
  destruct (Z.max_spec 0 n) as [[? Hn] | [? Hn]]; rewrite Hn in *; omega.
Qed.

Hint Resolve cstring_local_facts : saturate_local.

Lemma cstringn_valid_pointer: forall s n p, cstringn s n p |-- valid_pointer p.
Proof.
  intros.
  entailer!. (* Why doesn't this bring in the local facts? *)
  eapply saturate_aux21.
  { apply cstringn_local_facts. }
  { auto. }
  unfold cstringn; Intros.
  apply data_at_valid_ptr; auto.
  unfold tarray; simpl.
  pose proof (Zlength_nonneg (string_to_Z s)).
  rewrite Z.max_r; omega.
Qed.

Hint Resolve cstring_valid_pointer : valid_pointer.

End CS.
