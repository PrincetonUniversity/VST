Require Import VST.floyd.proofauto.
Require Import Coq.Program.Tactics.

Lemma strcat_clause : forall n ld,
  map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef =
    map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef.
Proof.
  (* This is not provable. This data_at version need data_at any |-- data_at Vundef *)
  intros.
  rewrite !map_app. rewrite <- app_assoc.
Admitted.

Lemma strcat_undef : forall n (ld ls : list val),
  Zlength ld + Zlength ls < n ->
  sublist 1 (Zlength (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef))
  (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) = list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros. list_normalize. f_equal. Zlength_solve.
Qed.

Lemma strcat_loop2 : forall n x (ld ls : list byte),
  0 <= x < Zlength ls ->
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ sublist 0 x ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero]))))) =
  map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef.
Proof.
  intros. fold_Vbyte.
  list_normalize.
  repeat list_deduce.
  all : f_equal; Zlength_solve.
Qed.

Ltac Zlength_solve ::= show_goal; autorewrite with Zlength; pose_Zlength_nonneg; omega.

Hint Rewrite Zlength_rev using Zlength_solve : Zlength.
Lemma revarray_same_length : forall j contents,
  0 <= j <= Zlength contents - j ->
  Zlength
  (sublist 0 j (rev (map Vint contents)) ++
   sublist j (Zlength (map Vint contents) - j) (map Vint contents) ++
   sublist (Zlength (map Vint contents) - j) (Zlength (map Vint contents)) (rev (map Vint contents))) =
Zlength (map Vint (rev contents)).
Proof.
  intros. Zlength_solve.
 


