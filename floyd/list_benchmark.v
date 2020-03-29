Require Import VST.floyd.proofauto.
Require Import VST.floyd.list_solver.
Open Scope logic.

Require Import Coq.Program.Tactics.


Example strcat_preloop2 : forall {cs : compspecs} n ld,
  n > Zlength ld ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
    (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  intros.
  list_form. apply_list_ext. Znth_solve.
Qed.

Example strcat_return : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros.
  list_form. apply_list_ext. Znth_solve.
Qed.

Example strcat_loop2 : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  intros. fold_Vbyte.
  apply_list_ext. list_form. Znth_solve.
Qed.

Example strcpy_return : forall {cs : compspecs} sh n ls dest,
  Zlength ls < n ->
  data_at sh (tarray tschar n)
  (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero)))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef) dest.
Proof.
  intros.
  list_form. apply_list_ext. Znth_solve.
Qed.

Example strcpy_loop : forall {cs : compspecs} sh n x ls dest,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  data_at sh (tarray tschar n)
  (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef) dest.
Proof.
  intros.
  list_form. Znth_solve2.
  fold_Vbyte. apply_list_ext. Znth_solve.
Qed.
