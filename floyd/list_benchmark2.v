Require Import VST.floyd.proofauto.
Require Import VST.floyd.list_solver2.
Open Scope logic.

Require Import Coq.Program.Tactics.

Example highly_dependent_example : forall (al bl : list Z),
  Zlength al > 0 ->
  Zlength bl = Zlength al ->
  Zlength (upd_Znth 0 (upd_Znth 0 (upd_Znth 0 al 1) 1) 1)
  = Zlength (upd_Znth 0 (upd_Znth 0 (upd_Znth 0 bl 1) 1) 1).
Proof.
  idtac "highly_dependent_example".
  intros.
  list_form.
  Time Zlength_solve.
Time Qed.

Example strcat_preloop2 : forall {cs : compspecs} n ld,
  n > Zlength ld ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
    (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  idtac "strcat_preloop2".
  intros. list_form.
  Time apply_list_ext.
  Time Znth_solve.
Time Qed.

Example strcat_return : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  idtac "strcat_return".
  intros. list_form.
  Time apply_list_ext.
  Time Znth_solve.
Time Qed.

Example strcat_loop2 : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  idtac "strcat_loop2".
  intros. fold_Vbyte. list_form.
  Time apply_list_ext.
  Time Znth_solve.
Time Qed.

Example strcpy_return : forall {cs : compspecs} sh n ls dest,
  Zlength ls < n ->
  data_at sh (tarray tschar n)
  (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero)))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef) dest.
Proof.
  idtac "strcpy_return".
  intros. list_form.
  Time apply_list_ext.
  Time Znth_solve.
Time Qed.

Example strcpy_loop : forall {cs : compspecs} sh n x ls dest,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  data_at sh (tarray tschar n)
  (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef) dest.

Proof.
  idtac "strcpy_loop".
  intros. fold_Vbyte. list_form.
  Time Znth_solve2.
  Time apply_list_ext.
  Time Znth_solve.
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
  idtac "strcmp_loop".
  intros.
  list_form. range_form.
  Time split3; intros; Znth_solve2; try omega; range_saturate; try congruence; fassumption.
  (* New version : Finished transaction in 2.253 secs (2.25u,0.s) (successful) *)
  (* Old version : Finished transaction in 1.383 secs (1.375u,0.s) (successful) *)
Time Qed.

Require Import VST.floyd.library.
Require Import VST.progs.rotate.
Require Import VST.floyd.Funspec_old_Notation.

Section verif_rotate.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* auxilary *)

Lemma Forall_range_uni : forall {X} {d : Inhabitant X} l P,
  Forall P l -> range_uni 0 (Zlength l) l P.
Proof.
  intros. induction H; unfold range_uni, rangei in *; intros.
  - list_solve2.
  - destruct (Z_le_lt_dec i 0).
    + list_solve2.
    + exploit (IHForall (i-1)); list_solve2.
Qed.

(* end auxilary *)

Definition rotate {X} (l : list X) k :=
  sublist k (Zlength l) l ++ sublist 0 k l.

Definition rotate_spec :=
 DECLARE _rotate
  WITH sh : share, a : val, s : list Z, n : Z, k : Z, gv : globals
  PRE [ _a OF (tptr tint) , _n OF (tint), _k OF (tint)]
     PROP(writable_share sh; 0 <= n; 0 <= 4 * n <= Ptrofs.max_unsigned;
        0 < k < n
     )
     LOCAL (temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
     SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  POST [ tvoid ]
     PROP()
     LOCAL()
     SEP (mem_mgr gv; (data_at sh (tarray tint n) (map Vint (map Int.repr (rotate s k))) a)).

Arguments sorted {_ _}.

Definition sorted_rotate (l : list Z) k N :=
  sublist k (Zlength l) l ++ map (Z.add N) (sublist 0 k l).

Definition sorted_rotate_spec :=
 DECLARE _sorted_rotate
  WITH sh : share, a : val, s : list Z, n : Z, k : Z, N : Z, gv : globals
  PRE [ _a OF (tptr tint) , _n OF (tint), _k OF (tint), _N OF (tint)]
     PROP(writable_share sh; 0 <= n; 0 <= 4 * n <= Ptrofs.max_unsigned;
        0 < k < n; 0 <= N*2 < Int.max_signed;
        Forall (fun x => 0 <= x <= N) s;
        sorted Z.le s
     )
     LOCAL (temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); temp _N (Vint (Int.repr N)); gvars gv)
     SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  POST [ tvoid ]
     PROP(sorted Z.le (sorted_rotate s k N))
     LOCAL()
     SEP (mem_mgr gv; (data_at sh (tarray tint n) (map Vint (map Int.repr (sorted_rotate s k N))) a)).

Definition Gprog : funspecs :=
        ltac:(with_library prog [rotate_spec; sorted_rotate_spec]).


Lemma rotate_body : semax_body Vprog Gprog f_rotate rotate_spec.
Proof.
  idtac "rotate_body".
  start_function.
  forward_call (tarray tint n, gv).
  { simpl. autorewrite with sublist. auto. }
  Intros b.
  forward_if (
    PROP ( )
    LOCAL (temp _b b; temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tint n) b; data_at_ Ews (tarray tint n) b;
      data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  ).
  { if_tac; entailer!. }
  { forward_call (-1). inv H3. }
  { forward. entailer!. if_tac; auto. congruence. }
  freeze [0; 1] FR.
  assert_PROP (n = Zlength s). { entailer!. Time list_solve2. }
  forward_for_simple_bound (n-k) (EX i : Z,
    PROP ( )
    LOCAL (temp _b b; temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tint n) (map Vint (map Int.repr (sublist k (k+i) s)) ++ Zrepeat Vundef (n-i)) b; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  ).
  { entailer!. rewrite data_at__tarray. Time list_solve2. }
  { forward.
    forward.
    entailer!.
    Time list_solve2.
  }
  forward_for_simple_bound n (EX i : Z,
    PROP (n-k <= i)
    LOCAL (temp _b b; temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tint n) (map Vint (map Int.repr (sublist k n s ++ sublist 0 (i-(n-k)) s)) ++ Zrepeat Vundef (n-i)) b;
      data_at sh (tarray tint n) (map Vint (map Int.repr s)) a
    )
  ).
  { forward. Exists (n-k). entailer!. Time list_solve2. }
  { Intros.
    forward.
    forward.
    entailer!.
    Time list_solve2.
  }
  forward_for_simple_bound n (EX i : Z,
    PROP ( )
    LOCAL (temp _b b; temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tint n) (map Vint (map Int.repr (sublist k n s ++ sublist 0 k s))) b;
      data_at sh (tarray tint n) (map Vint (map Int.repr (sublist 0 i (sublist k n s ++ sublist 0 k s) ++ sublist i n s))) a
    )
  ).
  { entailer!. Time apply sepcon_derives; list_solve2. }
  { forward.
    forward.
    entailer!.
    Time list_solve2.
  }
  thaw FR.
  forward_call (tarray tint n, b, gv).
  { if_tac; entailer!. }
  entailer!.
  unfold rotate.
  Time list_solve2.
Time Qed.

Lemma sorted_rotate_body : semax_body Vprog Gprog f_sorted_rotate sorted_rotate_spec.
Proof.
  idtac "sorted_rotate_body".
  start_function.
  assert_PROP (Zlength s = n). { entailer!. list_solve2. }
  remember (sublist 0 k s) as s1.
  remember (sublist k n s) as s2.
  assert (Zlength s1 = k) by (subst; list_solve2).
  assert (Zlength s2 = n-k) by (subst; list_solve2).
  assert (s = s1 ++ s2) by (subst; list_solve2).
  clear Heqs1 Heqs2. subst s.
  apply Forall_range_uni in H3.
  forward_call (sh, a, s1 ++ s2, n, k, gv).
  unfold rotate.
  forward_for_simple_bound n (EX i : Z,
    PROP (n-k <= i <= n)
    LOCAL (temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); temp _N (Vint (Int.repr N)); gvars gv)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr (
      s2
        ++ map (fun x => x + N) (sublist 0 (i-(n-k)) s1)
        ++ sublist (i-(n-k)) k s1)
    )) a)
  ).
  { forward. Exists (n-k). entailer!. Time list_solve2. }
  { Intros.
    forward.
    exploit (H3 (i-(n-k))). Time list_solve2. intros.
    forward.
    { entailer!. autorewrite with Znth in *.
      replace (Znth _ s1) with (Znth (i - (Zlength (s1 ++ s2) - Zlength s1)) s1) by list_solve2.
      do 2 rewrite Int.signed_repr by rep_omega. rep_omega.
    }
    entailer!. Time list_solve2.
  }
  unfold sorted_rotate. entailer!.
  {
    unfold sorted. intros.
    Time list_prop_solve'.
  }
  {
    Time list_solve2'.
    (* A proof goal is remained because the base solver is incomplete. *)
    apply data_subsume_refl'. rewrite Z.add_comm. repeat f_equal. Time list_solve.
  }
Time Qed.

End verif_rotate.
