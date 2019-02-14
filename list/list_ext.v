Require Import VST.floyd.proofauto.

Lemma strcat_loop2 : forall n x (ld ls : list byte),
  0 <= x < Zlength ls ->
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ sublist 0 x ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero]))))) =
  map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef.
Proof.
  intros. fold_Vbyte. list_form.
  apply (Znth_eq_ext _ Inhabitant_val).
  - Zlength_solve.
  - autorewrite with Zlength. intros.
    Znth_solve.
    + do 2 f_equal. Zlength_solve.
Qed.

