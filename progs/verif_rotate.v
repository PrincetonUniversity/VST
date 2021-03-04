Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.rotate.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition rotate {X} (l : list X) k :=
  sublist k (Zlength l) l ++ sublist 0 k l.

Definition rotate_spec :=
 DECLARE _rotate
  WITH sh : share, a : val, s : list Z, n : Z, k : Z, gv : globals
  PRE [ tptr tint , tint, tint]
     PROP(writable_share sh; 0 <= n; 0 <= 4 * n <= Ptrofs.max_unsigned;
        0 < k < n
     )
     PARAMS (a; Vint (Int.repr n); Vint (Int.repr k)) GLOBALS (gv)
     SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  POST [ tvoid ]
     PROP()
     RETURN()
     SEP (mem_mgr gv; (data_at sh (tarray tint n) (map Vint (map Int.repr (rotate s k))) a)).

Arguments sorted {_ _}.

Definition sorted_rotate (l : list Z) k N :=
  sublist k (Zlength l) l ++ map (Z.add N) (sublist 0 k l).

Definition sorted_rotate_spec :=
 DECLARE _sorted_rotate
  WITH sh : share, a : val, s : list Z, n : Z, k : Z, N : Z, gv : globals
  PRE [ tptr tint , tint, tint, tint]
     PROP(writable_share sh; 0 <= n; 0 <= 4 * n <= Ptrofs.max_unsigned;
        0 < k < n; 0 <= N*2 < Int.max_signed;
        Forall (fun x => 0 <= x <= N) s;
        sorted Z.le s
     )
     PARAMS (a; Vint (Int.repr n); Vint (Int.repr k); Vint (Int.repr N)) GLOBALS (gv)
     SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  POST [ tvoid ]
     PROP(sorted Z.le (sorted_rotate s k N))
     RETURN()
     SEP (mem_mgr gv; (data_at sh (tarray tint n) (map Vint (map Int.repr (sorted_rotate s k N))) a)).

Definition Gprog : funspecs :=
        ltac:(with_library prog [rotate_spec; sorted_rotate_spec]).

Lemma rotate_body : semax_body Vprog Gprog f_rotate rotate_spec.
Proof.
  start_function.
  forward_call (tarray tint n, gv).
  simpl; lia.
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
    Time list_solve.
  }
  forward_for_simple_bound n (EX i : Z,
    PROP (n-k <= i)
    LOCAL (temp _b b; temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tint n) (map Vint (map Int.repr (sublist k n s ++ sublist 0 (i-(n-k)) s)) ++ Zrepeat Vundef (n-i)) b;
      data_at sh (tarray tint n) (map Vint (map Int.repr s)) a
    )
  ).
  { forward. Exists (n-k). entailer!. list_solve. }
  { Intros.
    forward.
    forward.
    entailer!.
    Time list_solve.
  }
  forward_for_simple_bound n (EX i : Z,
    PROP ( )
    LOCAL (temp _b b; temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)); gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tint n) (map Vint (map Int.repr (sublist k n s ++ sublist 0 k s))) b;
      data_at sh (tarray tint n) (map Vint (map Int.repr (sublist 0 i (sublist k n s ++ sublist 0 k s) ++ sublist i n s))) a
    )
  ).
  { entailer!. apply sepcon_derives; list_solve. }
  { forward.
    forward.
    entailer!.
    Time list_solve.
  }
  thaw FR.
  forward_call (tarray tint n, b, gv).
  { if_tac; entailer!. }
  entailer!.
  unfold rotate.
  Time list_solve.
Time Qed.

Lemma sorted_rotate_body : semax_body Vprog Gprog f_sorted_rotate sorted_rotate_spec.
Proof.
  start_function.
  assert_PROP (Zlength s = n). { entailer!. list_solve. }
  remember (sublist 0 k s) as s1.
  remember (sublist k n s) as s2.
  assert (Zlength s1 = k) by (subst; list_solve).
  assert (Zlength s2 = n-k) by (subst; list_solve).
  assert (s = s1 ++ s2) by (subst; list_solve).
  clear Heqs1 Heqs2. subst s.
  apply Forall_forall_range in H3.
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
  { forward. Exists (n-k). entailer!. list_solve. }
  { Intros.
    forward.
    exploit (H3 (i-(n-k))). list_solve. intros.
    forward.
    { entailer!. autorewrite with Znth in *.
      replace (Znth _ s1) with (Znth (i - (Zlength (s1 ++ s2) - Zlength s1)) s1) by list_solve.
      do 2 rewrite Int.signed_repr by rep_lia. rep_lia.
    }
    entailer!. Time list_solve.
  }
  unfold sorted_rotate. entailer!.
  {
    unfold sorted. intros.
    Time list_prop_solve'.
  }
  {
    Time list_solve.
  }
Time Qed.
