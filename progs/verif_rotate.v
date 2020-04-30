Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.rotate.
Require Import VST.floyd.Funspec_old_Notation.

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
  assert_PROP (n = Zlength s). { entailer!. list_solve. }
  forward_for_simple_bound (n-k) (EX i : Z,
    PROP ( )
    LOCAL (temp _b b; temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tint n) (map Vint (map Int.repr (sublist k (k+i) s)) ++ Zrepeat Vundef (n-i)) b; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  ).
  { entailer!. rewrite data_at__tarray. list_solve. }
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
  { forward. Exists (n-k). entailer!. list_solve2. }
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
  { entailer!. apply sepcon_derives; list_solve2. }
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
  start_function.
  assert_PROP (Zlength s = n). { entailer!. list_solve. }
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
  { forward. Exists (n-k). entailer!. list_solve2. }
  { Intros.
    forward.
    exploit (H3 (i-(n-k))). list_solve2. intros.
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
    apply data_subsume_refl'. rewrite Z.add_comm. repeat f_equal. list_solve.
  }
Time Qed.
