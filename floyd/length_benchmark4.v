Require Import VST.floyd.proofauto.
Require Import VST.floyd.list_solver4.
Open Scope logic.

Require Import Coq.Program.Tactics.

Ltac list_solver.Zlength_solve ::= Zlength_solve.

Example strcat_preloop2 : forall n ld,
  n > Zlength ld ->
  Zlength (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
  = Zlength (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  idtac "strcat_preloop2".
  intros.
  list_form.
  Time Zlength_solve.
Time Qed.

Example strcat_preloop2' : forall n ld,
  n > Zlength ld ->
  n = Zlength (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
  .
Proof.
  idtac "strcat_preloop2".
  intros.
  list_form.
  Time Zlength_solve.
Time Qed.

Example strcat_return : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  Zlength (map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero]))))) =
  Zlength (map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef).
Proof.
  idtac "strcat_return".
  intros.
  list_form.
  Time Zlength_solve.
Time Qed.

Example strcat_loop2 : forall n x ld ls,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  Zlength (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero]))))))
  = Zlength (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef).
Proof.
  idtac "strcat_loop2".
  intros.
  list_form.
  Time Zlength_solve.
Time Qed.

Example strcpy_return : forall n ls,
  Zlength ls < n ->
  Zlength (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero))))
  = Zlength (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef).
Proof.
  idtac "strcpy_return".
  intros.
  list_form.
  Time Zlength_solve.
Time Qed.

Example strcpy_loop : forall n x ls,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  Zlength (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero]))))))
  = Zlength (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef).
Proof.
  idtac "strcpy_loop".
  intros.
  list_form.
  Time Znth_solve2.
Time Qed.
