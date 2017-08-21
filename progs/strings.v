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
