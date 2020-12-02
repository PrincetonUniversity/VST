Require Import VST.floyd.proofauto.
(* Require Import VST.floyd.list_solver. *)
(* Require Import VST.floyd.data_at_list_solver. *)
Open Scope logic.

Require Import Coq.Program.Tactics.

Example highly_nested_length_example : forall (al bl : list Z),
  Zlength al > 0 ->
  Zlength bl = Zlength al ->
  Zlength (upd_Znth 0 (upd_Znth 0 (upd_Znth 0 al 1) 1) 1)
  = Zlength (upd_Znth 0 (upd_Znth 0 (upd_Znth 0 bl 1) 1) 1).
Proof.
  idtac "highly_nested_length_example (length goal)".
  intros.
  Time list_solve.
Time Qed.

Example strcat_preloop2 : forall {cs : compspecs} n ld,
  n > Zlength ld ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
    (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  idtac "strcat_preloop2 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example strcat_return : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  idtac "strcat_return (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example strcat_loop2 : forall {cs : compspecs} n x ld ls,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ sublist 0 x ls) ++
      upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero]))))))
    (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef).
Proof.
  idtac "strcat_loop2 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example strcpy_return : forall {cs : compspecs} n ls,
  Zlength ls < n ->
  data_subsume (tarray tschar n)
    (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero))))
    (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef).
Proof.
  idtac "strcpy_return (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example strcpy_loop : forall {cs : compspecs} n x ls,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  data_subsume (tarray tschar n)
    (map Vbyte (sublist 0 x ls) ++
      upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero]))))))
    (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef).
Proof.
  idtac "strcpy_loop (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

(* This is a very hard case, a lot of deductions are needed *)
(* cool automation now! *)
Example strcmp_loop : forall i ls1 ls2,
  ~ In Byte.zero ls1 ->
  ~ In Byte.zero ls2 ->
  0 <= i < Zlength ls1 + 1 ->
  0 <= i < Zlength ls2 + 1 ->
  (forall j : Z, 0 <= j < i -> Znth j ls1 = Znth j ls2) ->
  i <> Zlength ls1 \/ i <> Zlength ls2 ->
  Znth i (ls1 ++ [Byte.zero]) = Znth i (ls2 ++ [Byte.zero]) ->
  i + 1 < Zlength ls1 + 1 /\
  i + 1 < Zlength ls2 + 1 /\
  forall j : Z, 0 <= j < i + 1 -> Znth j ls1 = Znth j ls2.
Proof.
  idtac "strcmp_loop (array prop goal)".
  intros.
  Time list_solve.
Time Qed.

Section verif_rotate.

(* auxilary *)

Lemma Forall_forall_range : forall {X} {d : Inhabitant X} l P,
  Forall P l -> forall_range 0 (Zlength l) l P.
Proof.
  intros. induction H; unfold forall_range, rangei in *; intros.
  - list_solve2.
  - destruct (Z_le_lt_dec i 0).
    + list_solve2.
    + exploit (IHForall (i-1)); list_solve2.
Qed.

(* end auxilary *)

Definition rotate {X} (l : list X) k :=
  sublist k (Zlength l) l ++ sublist 0 k l.

Definition sorted_rotate (l : list Z) k N :=
  sublist k (Zlength l) l ++ map (Z.add N) (sublist 0 k l).

Example rotate_length1 : forall s,
  Zlength (map Vint (map Int.repr s)) = Zlength s.
Proof.
  idtac "rotate_length1 (length goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array1 : forall {cs : compspecs} k s,
  0 < k < Zlength s ->
  data_subsume (tarray tint (Zlength s))
    (list_repeat (Z.to_nat (Zlength s)) Vundef)
    (map Vint (map Int.repr (sublist k k s)) ++ Zrepeat Vundef (Zlength s)).
Proof.
  idtac "rotate_array1 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array2 : forall {cs : compspecs} k i s,
  0 < k < Zlength s ->
  0 <= i < Zlength s - k ->
  data_subsume (tarray tint (Zlength s))
    (upd_Znth i
      (map Vint (map Int.repr (sublist k (k + i) s)) ++
        Zrepeat Vundef (Zlength s - i)) (Vint (Int.repr (Znth (i + k) s))))
    (map Vint (map Int.repr (sublist k (k + (i + 1)) s)) ++
        Zrepeat Vundef (Zlength s - (i + 1))).
Proof.
  idtac "rotate_array2 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array3 : forall {cs : compspecs} k s,
  0 < k < Zlength s ->
  data_subsume (tarray tint (Zlength s))
    (map Vint (map Int.repr (sublist k (k + (Zlength s - k)) s)) ++
      Zrepeat Vundef (Zlength s - (Zlength s - k)))
    (map Vint
      (map Int.repr
          (sublist k (Zlength s) s ++
          sublist 0 (Zlength s - k - (Zlength s - k)) s)) ++
    Zrepeat Vundef (Zlength s - (Zlength s - k))).
Proof.
  idtac "rotate_array3 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array4 : forall {cs : compspecs} k i s,
  0 < k < Zlength s ->
  Zlength s - k <= i < Zlength s ->
  data_subsume (tarray tint (Zlength s))
    (upd_Znth i
      (map Vint
          (map Int.repr
            (sublist k (Zlength s) s ++ sublist 0 (i - (Zlength s - k)) s)) ++
        Zrepeat Vundef (Zlength s - i))
      (Vint (Int.repr (Znth (i + k - Zlength s) s))))
    (map Vint
      (map Int.repr
          (sublist k (Zlength s) s ++ sublist 0 (i + 1 - (Zlength s - k)) s)) ++
    Zrepeat Vundef (Zlength s - (i + 1))).
Proof.
  idtac "rotate_array4 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array5 : forall {cs : compspecs} k s,
  0 < k < Zlength s ->
  data_subsume (tarray tint (Zlength s))
    (map Vint
      (map Int.repr
          (sublist k (Zlength s) s ++ sublist 0 (Zlength s - (Zlength s - k)) s)) ++
    Zrepeat Vundef (Zlength s - Zlength s))
    (map Vint (map Int.repr (sublist k (Zlength s) s ++ sublist 0 k s))).
Proof.
  idtac "rotate_array5 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array6 : forall {cs : compspecs} k s,
  0 < k < Zlength s ->
  data_subsume (tarray tint (Zlength s))
    (map Vint (map Int.repr s))
    (map Vint
      (map Int.repr
          (sublist 0 0 (sublist k (Zlength s) s ++ sublist 0 k s) ++
          sublist 0 (Zlength s) s))).
Proof.
  idtac "rotate_array6 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array7 : forall {cs : compspecs} k i s,
  0 < k < Zlength s ->
  0 <= i < Zlength s ->
  data_subsume (tarray tint (Zlength s))
    (upd_Znth i
      (map Vint
          (map Int.repr
            (sublist 0 i (sublist k (Zlength s) s ++ sublist 0 k s) ++
              sublist i (Zlength s) s)))
      (Vint (Int.repr (Znth i (sublist k (Zlength s) s ++ sublist 0 k s)))))
    (map Vint
      (map Int.repr
          (sublist 0 (i + 1) (sublist k (Zlength s) s ++ sublist 0 k s) ++
          sublist (i + 1) (Zlength s) s))).
Proof.
  idtac "rotate_array7 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example rotate_array8 : forall {cs : compspecs} k s,
  0 < k < Zlength s ->
  data_subsume (tarray tint (Zlength s))
    (map Vint
      (map Int.repr
          (sublist 0 (Zlength s) (sublist k (Zlength s) s ++ sublist 0 k s) ++
          sublist (Zlength s) (Zlength s) s)))
    (map Vint (map Int.repr (sublist k (Zlength s) s ++ sublist 0 k s))).
Proof.
  idtac "rotate_array8 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_length1 : forall s,
  Zlength s = Zlength (map Vint (map Int.repr s)).
Proof.
  idtac "sorted_rotate_length1 (length goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_length2 : forall (s : list Z) k,
  0 < k < Zlength s ->
  Zlength (sublist 0 k s) = k.
Proof.
  idtac "sorted_rotate_length2 (length goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_length3 : forall (s : list Z) k,
  0 < k < Zlength s ->
  Zlength (sublist k (Zlength s) s) = Zlength s - k.
Proof.
  idtac "sorted_rotate_length3 (length goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_array1 : forall (s : list Z) k,
  0 < k < Zlength s ->
  s = sublist 0 k s ++ sublist k (Zlength s) s.
Proof.
  idtac "sorted_rotate_array1 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_array2 : forall {cs : compspecs} s1 s2 N,
  data_subsume (tarray tint (Zlength (s1 ++ s2)))
    (map Vint
      (map Int.repr
          (sublist (Zlength s1) (Zlength (s1 ++ s2)) (s1 ++ s2) ++
          sublist 0 (Zlength s1) (s1 ++ s2))))
    (map Vint
      (map Int.repr
          (s2 ++
          map (fun x : Z => x + N)
            (sublist 0
                (Zlength (s1 ++ s2) - Zlength s1 -
                (Zlength (s1 ++ s2) - Zlength s1)) s1) ++
          sublist
            (Zlength (s1 ++ s2) - Zlength s1 -
              (Zlength (s1 ++ s2) - Zlength s1))
            (Zlength s1) s1))).
Proof.
  idtac "sorted_rotate_array2 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_length4 : forall (s1 s2 : list Z) n k i,
  Zlength (s1 ++ s2) = n ->
  Zlength s1 = k ->
  Zlength s2 = n - k ->
  n - k <= i < n ->
  0 <= i - (n - k) < Zlength (s1 ++ s2).
Proof.
  idtac "sorted_rotate_length4 (length goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_array3 : forall {cs : compspecs} s1 s2 N i,
  Zlength (s1 ++ s2) - Zlength s1 <= i < Zlength (s1 ++ s2) ->
  data_subsume (tarray tint (Zlength (s1 ++ s2)))
    (upd_Znth i
      (map Vint
          (map Int.repr
            (s2 ++
              map (fun x : Z => x + N)
                (sublist 0 (i - (Zlength (s1 ++ s2) - Zlength s1)) s1) ++
              sublist (i - (Zlength (s1 ++ s2) - Zlength s1)) (Zlength s1) s1)))
      (Vint
          (Int.repr
            (Znth i
                (s2 ++
                map (fun x : Z => x + N)
                  (sublist 0 (i - (Zlength (s1 ++ s2) - Zlength s1)) s1) ++
                sublist (i - (Zlength (s1 ++ s2) - Zlength s1))
                  (Zlength s1) s1) + N))))
    (map Vint
      (map Int.repr
          (s2 ++
          map (fun x : Z => x + N)
            (sublist 0 (i + 1 - (Zlength (s1 ++ s2) - Zlength s1)) s1) ++
          sublist (i + 1 - (Zlength (s1 ++ s2) - Zlength s1))
            (Zlength s1) s1))).
Proof.
  idtac "sorted_rotate_array3 (qf-array goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_array_prop : forall s1 s2 N,
  sorted Z.le (s1 ++ s2) ->
  forall_range 0 (Zlength (s1 ++ s2)) (s1 ++ s2) (fun x : Z => 0 <= x <= N) ->
  forall i j : Z,
  0 <= i <= j /\
  j <
  Zlength
    (sublist (Zlength s1) (Zlength (s1 ++ s2)) (s1 ++ s2) ++
    map (Z.add N) (sublist 0 (Zlength s1) (s1 ++ s2))) ->
  Znth i
    (sublist (Zlength s1) (Zlength (s1 ++ s2)) (s1 ++ s2) ++
    map (Z.add N) (sublist 0 (Zlength s1) (s1 ++ s2))) <=
  Znth j
    (sublist (Zlength s1) (Zlength (s1 ++ s2)) (s1 ++ s2) ++
    map (Z.add N) (sublist 0 (Zlength s1) (s1 ++ s2))).
Proof.
  idtac "sorted_rotate_array_prop (array prop goal)".
  intros.
  Time list_solve.
Time Qed.

Example sorted_rotate_array4 : forall s1 s2 N,
  map Vint
    (map Int.repr
      (s2 ++
        map (fun x : Z => x + N)
          (sublist 0 (Zlength (s1 ++ s2) - (Zlength (s1 ++ s2) - Zlength s1))
            s1) ++
        sublist (Zlength (s1 ++ s2) - (Zlength (s1 ++ s2) - Zlength s1))
          (Zlength s1) s1)) =
  map Vint
    (map Int.repr
      (sublist (Zlength s1) (Zlength (s1 ++ s2)) (s1 ++ s2) ++
        map (Z.add N) (sublist 0 (Zlength s1) (s1 ++ s2)))).
Proof.
  idtac "sorted_rotate_array4 (qf-array goal)".
  intros.
  (* Not directly solvable by list_solve, because of the incompleteness of the base solver. *)
  Time list_simplify.
  rewrite Z.add_comm. Time list_solve.
Time Qed.

End verif_rotate.
