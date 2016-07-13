Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.general_lemmas.

Lemma data_at_weak_valid_ptr: forall (sh : Share.t) (t : type) (v : reptype t) (p : val),
       sepalg.nonidentity sh ->
       sizeof (*cenv_cs*) t >= 0 -> data_at sh t v p |-- weak_valid_pointer p.
Proof.
Admitted.
Lemma sepcon_weak_valid_pointer2
: forall (P Q : mpred) (p : val),
    P |-- weak_valid_pointer p -> Q * P |-- weak_valid_pointer p.
Proof. Admitted.
Lemma sepcon_weak_valid_pointer1
: forall (P Q : mpred) (p : val),
    P |-- weak_valid_pointer p -> P * Q |-- weak_valid_pointer p.
Proof. Admitted.
Hint Resolve sepcon_weak_valid_pointer1 sepcon_weak_valid_pointer2 data_at_weak_valid_ptr: valid_pointer.

Lemma sublist_app_exact1:
  forall X (A B: list X), sublist 0 (Zlength A) (A ++ B) = A.
Proof.
  intros.
  pose proof (Zlength_nonneg A).
  rewrite sublist_app1; try omega.
  rewrite sublist_same; auto.
Qed.

Lemma sublist_app_exact2:
  forall X (A B: list X), sublist (Zlength A) (Zlength A + Zlength B) (A ++ B) = B.
Proof.
  intros.
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  rewrite sublist_app2; try omega.
  rewrite sublist_same; auto; omega.
Qed.

Lemma isbyteZ_app: forall A B, Forall general_lemmas.isbyteZ A -> Forall general_lemmas.isbyteZ B -> Forall isbyteZ (A ++ B).
Proof.
  intros A B HA HB.
  induction A as [|hdA tlA].
  simpl; assumption.
  simpl. inversion HA. constructor.
  assumption.
  apply IHtlA.
  assumption.
Qed.

Lemma data_at_complete_split:
  forall A B lengthA lengthB AB length p offset sh,
    field_compatible (tarray tuchar (Zlength A + Zlength B)) [] p ->
    lengthA = Zlength A ->
    lengthB = Zlength B ->
    length = lengthA + lengthB ->
    offset = lengthA ->
    AB = A ++ B ->
    (data_at sh (tarray tuchar length) (AB) p) = (data_at sh (tarray tuchar lengthA) A p) * (data_at sh (tarray tuchar lengthB) B (offset_val offset p)).
Proof.
  intros until sh.
  intros Hfield.
  intros; subst.
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  assert (Hisptr: isptr p) by (destruct Hfield; assumption).
  destruct p; try solve [inversion Hisptr]; clear Hisptr.
  unfold tarray.
  rewrite split2_data_at_Tarray_tuchar with (n1:=Zlength A); [|split; omega|rewrite Zlength_app; reflexivity].
  rewrite sublist_app_exact1, sublist_app_exact2.
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by omega.
  replace (field_address0 (Tarray tuchar (Zlength A + Zlength B) noattr) [ArraySubsc (Zlength A)] (Vptr b i)) with (Vptr b (Int.add i (Int.repr (Zlength A)))).
  reflexivity.
  rewrite field_address0_offset.
  simpl. replace (0 + 1 * Zlength A) with (Zlength A) by omega. reflexivity.
  destruct Hfield as [Hfield1 [Hfield2 [Hfield3 [Hfield4 [Hfield5 [Hfield6 [Hfield7 Hfield8]]]]]]].
  unfold field_compatible0; repeat split; try assumption; auto; omega.
Qed.
