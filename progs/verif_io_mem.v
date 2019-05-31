Require Import VST.progs.io_mem.
Require Import VST.progs.io_mem_specs.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import ITree.ITree.
(*Import ITreeNotations.*)
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition putchars_spec := DECLARE _putchars putchars_spec.
Definition getchars_spec := DECLARE _getchars getchars_spec.

(* make a new exit_spec that only allows exit code 0 if the ITREE is fully used, or that exit is only done w/ 1,
and put empty itree in main_post *)

(* This tells us that exit(0) is never called, so if we terminate successfully, the postcondition of main
  must hold. *)
Definition exit_spec := DECLARE _exit
 WITH i : Z
 PRE [1%positive OF tint]
   PROP (repable_signed i; i <> 0) LOCAL(temp 1%positive (Vint (Int.repr i))) SEP()
 POST [ tvoid ]
   PROP(False) LOCAL() SEP().

Lemma div_10_dec : forall n, 0 < n ->
  (Z.to_nat (n / 10) < Z.to_nat n)%nat.
Proof.
  intros.
  change 10 with (Z.of_nat 10).
  rewrite <- (Z2Nat.id n) by omega.
  rewrite <- div_Zdiv by discriminate.
  rewrite !Nat2Z.id.
  apply Nat2Z.inj_lt.
  rewrite div_Zdiv, Z2Nat.id by omega; simpl.
  apply Z.div_lt; auto; omega.
Qed.

Program Fixpoint chars_of_Z (n : Z) { measure (Z.to_nat n) } : list int :=
  let n' := n / 10 in
  match n' <=? 0 with true => [Int.repr (n + char0)] | false => chars_of_Z n' ++ [Int.repr (n mod 10 + char0)] end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous.
  eapply Z.lt_le_trans, Z_mult_div_ge with (b := 10); omega.
Defined.

(* The function computed by print_intr *)
Program Fixpoint intr n { measure (Z.to_nat n) } : list int :=
  match n <=? 0 with
  | true => []
  | false => intr (n / 10) ++ [Int.repr (n mod 10 + char0)]
  end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous; omega.
Defined.

Definition replace_list {X} i (l : list X) (l' : list X) :=
  sublist 0 i l ++ l' ++ sublist (i + Zlength l') (Zlength l) l.

Definition print_intr_spec :=
 DECLARE _print_intr
  WITH sh : share, i : Z, buf : val, j : Z, contents : list val
  PRE [ _i OF tuint, _buf OF tptr tuchar, _j OF tint ]
    PROP (writable_share sh; 0 <= i <= Int.max_unsigned;
               0 <= j; j + Zlength (intr i) <= Zlength contents < Int.max_signed)
    LOCAL (temp _i (Vint (Int.repr i)); temp _buf buf; temp _j (Vint (Int.repr j)))
    SEP (data_at sh (tarray tuchar (Zlength contents)) contents buf)
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (j + Zlength (intr i)))))
    SEP (data_at sh (tarray tuchar (Zlength contents)) (replace_list j contents (map Vint (intr i))) buf).

Definition print_int_spec :=
 DECLARE _print_int
  WITH gv : globals, i : Z, tr : IO_itree
  PRE [ _i OF tuint ]
    PROP (0 <= i < 10000)
    LOCAL (gvars gv; temp _i (Vint (Int.repr i)))
    SEP (mem_mgr gv; ITREE (write_list (chars_of_Z i ++ [Int.repr newline]) ;; tr))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; ITREE tr).

Definition for_loop i z (body : Z -> itree IO_event bool) :=
  ITree.aloop (fun '(b, j) => if (b : bool) then inr true else if j <? z then inl (b <- body j ;; Ret (b, j + 1)) else inr false) (false, i).

Definition sum_Z l := fold_right Z.add 0 l.

Definition read_sum_inner n nums j :=
  if orb (10 <=? Znth j nums) (Znth j nums <? 0) then Ret true
  else write_list (chars_of_Z (n + sum_Z (sublist 0 (j + 1) nums)) ++ [Int.repr newline]);; Ret false.

Definition read_sum n lc : IO_itree :=
  ITree.aloop (fun '(b, n, lc) => if (b : bool) then inr tt else
  if zlt n 1000 then
    let nums := map (fun c => Int.unsigned c - char0) lc in
    inl (b <- for_loop 0 4 (read_sum_inner n nums) ;; if (b : bool) then Ret (true, n, lc) else
    lc' <- read_list 4;; Ret (false, n + sum_Z nums, lc'))
  else inr tt) (false, n, lc).

Definition main_itree := lc <- read_list 4;; read_sum 0 lc (* ;; exit 0 *).
(* !! Making exit an effect and requiring it to be called at the end of a program is a good
   way to get around the problem of dropping suffixes of an itree. *)

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre_ext prog main_itree nil gv
  POST [ tint ] PROP () LOCAL () SEP (mem_mgr gv; ITREE (Ret tt)).
(* making the post false forces user to call exit to terminate *)

(* override default spec for exit *)
Definition library_G  {cs: compspecs} prog :=
 let defs := prog_defs prog in
  try_spec "_malloc" malloc_spec' defs ++
  try_spec "_free" free_spec' defs.

Ltac with_library prog G :=
  let pr := eval unfold prog in prog in  
 let x := constr:(library_G pr ++ G) in
  let x := eval cbv beta delta [app library_G] in x in
  let x := simpl_prog_defs x in 
  let x := eval cbv beta iota zeta delta [try_spec] in x in 
  let x := eval simpl in x in 
    with_library' pr x.

Definition Gprog : funspecs := ltac:(with_library prog [putchars_spec; getchars_spec;
  exit_spec; print_intr_spec; print_int_spec; main_spec]).

Lemma divu_repr : forall x y,
  0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.divu (Int.repr x) (Int.repr y) = Int.repr (x / y).
Proof.
  intros; unfold Int.divu.
  rewrite !Int.unsigned_repr; auto.
Qed.

(*Opaque bind.

Opaque Nat.div Nat.modulo.*)

Lemma intr_eq : forall n, intr n =
  match n <=? 0 with
  | true => []
  | false => intr (n / 10) ++ [Int.repr (n mod 10 + char0)]
  end.
Proof.
  intros.
  unfold intr at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold intr.
  destruct n; reflexivity.
Qed.

(* missing from standard library *)
Lemma Zdiv_le_compat_r : forall m n p, p > 0 -> m <= n -> m / p <= n / p.
Proof.
  intros; unfold Z.div.
  pose proof (Z_div_mod m _ H) as Hm.
  pose proof (Z_div_mod n _ H) as Hn.
  destruct (Z.div_eucl m p), (Z.div_eucl n p).
  destruct Hm, Hn; subst.
  destruct (zle z z1); auto.
  assert (p * z1 + p <= p * z); try omega.
  rewrite <- Z.mul_succ_r.
  apply Zmult_le_compat_l; omega.
Qed.

Lemma intr_lt : forall n, 0 < n -> Zlength (intr (n / 10)) = Zlength (intr n) - 1.
Proof.
  intros.
  rewrite (intr_eq n).
  destruct (n <=? 0) eqn: Hn.
  { apply Zle_bool_imp_le in Hn; omega. }
  rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
Qed.

Lemma replace_list_nil : forall {X} i (l : list X), 0 <= i <= Zlength l -> replace_list i l [] = l.
Proof.
  intros; unfold replace_list.
  rewrite Zlength_nil, Z.add_0_r; simpl.
  rewrite sublist_rejoin, sublist_same by omega; auto.
Qed.

Lemma replace_list_upd_snoc : forall {X} i (l l' : list X) x, 0 <= i -> i + Zlength l' < Zlength l ->
  upd_Znth (i + Zlength l') (replace_list i l l') x = replace_list i l (l' ++ [x]).
Proof.
  intros; unfold replace_list.
  rewrite upd_Znth_app2; rewrite ?Zlength_sublist; try rep_omega.
  f_equal.
  rewrite Z.sub_0_r, Z.add_simpl_l, upd_Znth_app2; rewrite ?Zlength_sublist; try rep_omega.
  rewrite Zminus_diag, Zlength_app, Zlength_cons, Zlength_nil, upd_Znth0, <- app_assoc; simpl; f_equal; f_equal.
  rewrite Zlength_sublist by rep_omega.
  rewrite sublist_sublist by rep_omega.
  f_equal; omega.
  { rewrite Zlength_app, Zlength_sublist; rep_omega. }
Qed.

Lemma body_print_intr: semax_body Vprog Gprog f_print_intr print_intr_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP ()
    LOCAL (temp _k (Vint (Int.repr (j + Zlength (intr i) - 1))))
    SEP (data_at sh (tarray tuchar (Zlength contents)) (replace_list j contents (map Vint (intr i))) buf)).
  - forward.
    rewrite divu_repr by rep_omega.
    forward.
    forward_call (sh, i / 10, buf, j, contents).
    { rewrite intr_lt by omega; split; auto.
      assert (i / 10 < i).
      { apply Z.div_lt; omega. }
      split; [split|]; try omega.
      apply Z.div_pos; omega. }
    rewrite modu_repr by (omega || computable).
    forward.
    { entailer!.
      split; try rep_omega.
      rewrite intr_lt; omega. }
    entailer!.
    { rewrite intr_lt by omega.
      rewrite Z.add_sub_assoc; auto. }
    rewrite (intr_eq i).
    destruct (i <=? 0) eqn: Hi; [apply Zle_bool_imp_le in Hi; omega|].
    pose proof (Z_mod_lt i 10).
    rewrite <- (Zlength_map _ _ Vint), replace_list_upd_snoc.
    rewrite (zero_ext_inrange 8 (Int.repr (i mod 10))), add_repr.
    rewrite zero_ext_inrange, map_app.
    apply derives_refl.
    { rewrite Int.unsigned_repr; simpl; rep_omega. }
    { rewrite Int.unsigned_repr; simpl; rep_omega. }
    { omega. }
    { rewrite Zlength_map, intr_lt; rep_omega. }
  - forward.
    entailer!.
    (* spec has an off-by-one error *)
    { admit. }
    rewrite replace_list_nil by rep_omega; auto.
  - forward.
    rewrite Z.sub_simpl_r; entailer!.
Admitted.

Lemma chars_of_Z_eq : forall n, chars_of_Z n =
  let n' := n / 10 in
  match n' <=? 0 with true => [Int.repr (n + char0)] | false => chars_of_Z n' ++ [Int.repr (n mod 10 + char0)] end.
Proof.
  intros.
  unfold chars_of_Z at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold chars_of_Z.
  destruct (_ <=? _); reflexivity.
Qed.

Lemma chars_of_Z_intr : forall n,
  chars_of_Z n = if n <=? 0 then [Int.repr (n + char0)] else intr n.
Proof.
  intros.
  destruct (Z.leb_spec n 0).
  { rewrite chars_of_Z_eq; simpl.
    apply Zdiv_le_compat_r with (p := 10) in H; try omega.
    rewrite Zdiv_0_l in H.
    destruct (Z.leb_spec (n / 10) 0); auto; omega. }
  induction n as [? IH] using (well_founded_induction (Zwf.Zwf_well_founded 0)).
  rewrite chars_of_Z_eq, intr_eq.
  destruct (n <=? 0) eqn: Hn; [apply Zle_bool_imp_le in Hn; omega|].
  simpl.
  destruct (n / 10 <=? 0) eqn: Hdiv.
  - apply Zle_bool_imp_le in Hdiv.
    assert (0 <= n / 10).
    { apply Z.div_pos; omega. }
    assert (n / 10 = 0) as Hz by omega.
    rewrite Hz; simpl.
    apply Z.div_small_iff in Hz as [|]; try omega.
    rewrite Zmod_small; auto.
  - apply Z.leb_nle in Hdiv.
    rewrite IH; auto; try omega.
    split; try omega.
    apply Z.div_lt; auto; omega.
Qed.

Lemma intr_length : forall n a, 0 <= a -> n < Z.pow 10 a -> Zlength (intr n) <= a.
Proof.
  induction n using (well_founded_induction (Zwf.Zwf_well_founded 0)); intros.
  rewrite intr_eq.
  destruct (Z.leb_spec n 0); [rewrite Zlength_nil; omega|].
  rewrite Zlength_app.
  assert (Zlength (intr (n / 10)) <= a - 1); [|rewrite Zlength_cons, Zlength_nil; omega].
  assert (0 <= a - 1).
  { destruct (Z.eq_dec a 0); subst; simpl in *; omega. }
  apply H; auto.
  - split; try omega.
    apply Z.div_lt; auto; omega.
  - apply Zmult_lt_reg_r with 10; try omega.
    rewrite (Z.mul_comm (10 ^ _)), <- Z.pow_succ_r by auto.
    unfold Z.succ; rewrite Z.sub_simpl_r.
    eapply Z.le_lt_trans; eauto.
    rewrite Z.mul_comm; apply Z.mul_div_le; omega.
Qed.

Lemma chars_of_Z_length : forall n a, 0 < a -> n < Z.pow 10 a -> Zlength (chars_of_Z n) <= a.
Proof.
  intros.
  rewrite chars_of_Z_intr.
  destruct (Z.leb_spec n 0); [|apply intr_length; omega].
  rewrite Zlength_cons, Zlength_nil; omega.
Qed.

Lemma body_print_int: semax_body Vprog Gprog f_print_int print_int_spec.
Proof.
  start_function.
  forward_call (tarray tuchar 5, gv).
  { split; auto; simpl; computable. }
  Intro buf.
  forward_if (buf <> nullval).
  { if_tac; entailer!. }
  { forward_call 1.
    rep_omega.
    entailer!. }
  { forward.
    entailer!. }
  Intros; rewrite if_false by auto.
  forward_if (PROP ()
    LOCAL (temp _buf buf; gvars gv; temp _i (Vint (Int.repr i));
                 temp _k (Vint (Int.repr (Zlength (chars_of_Z i ++ [Int.repr newline])))))
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar 5) buf;
            data_at Ews (tarray tuchar 5) (map Vint (chars_of_Z i) ++ Vint (Int.repr newline) ::
              list_repeat (Z.to_nat (4 - Zlength (chars_of_Z i))) Vundef) buf;
            ITREE (write_list (chars_of_Z i ++ [Int.repr newline]);; tr))).
  - Intros.
    forward.
    forward.
    forward.
    entailer!.
  - Intros.
    sep_apply data_at__data_at.
    unfold default_val; simpl.
    assert (Zlength (intr i) <= 4).
    { apply intr_length; try omega.
      apply H. }
    forward_call.
    { rewrite !Zlength_cons, Zlength_nil.
      simpl; repeat (split; auto); rep_omega. }
    forward.
    { entailer!.
      rewrite !Zlength_cons, Zlength_nil; rep_omega. }
    forward.
    entailer!.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil, chars_of_Z_intr.
      destruct (Z.leb_spec i 0); auto; omega. }
    unfold replace_list; simpl.
    rewrite (sublist_list_repeat _ _ 5 Vundef).
    rewrite !Zlength_cons, Zlength_nil, Zlength_map; simpl.
    rewrite upd_Znth_app2.
    rewrite Zlength_map, Zminus_diag, upd_Znth0, sublist_list_repeat; try omega.
    apply derives_refl'.
    f_equal.
    rewrite chars_of_Z_intr.
    destruct (Z.leb_spec i 0); try omega.
    rewrite zero_ext_inrange.
    f_equal; f_equal; f_equal; f_equal.
    rewrite Zlength_list_repeat; try omega.
    { simpl; rewrite Int.unsigned_repr; rep_omega. }
    { rewrite Zlength_list_repeat; omega. }
    { rewrite Zlength_map, Zlength_list_repeat; omega. }
    { rewrite Zlength_map; rep_omega. }
    { rewrite !Zlength_cons, Zlength_nil, Zlength_map; omega. }
  - forward_call (Ews, buf, chars_of_Z i ++ [Int.repr newline],
      5, list_repeat (Z.to_nat (4 - Zlength (chars_of_Z i))) Vundef, tr).
    { rewrite map_app, <- app_assoc; simpl; cancel. }
    forward_call (tarray tuchar 5, buf, gv).
    { rewrite if_false by auto; cancel. }
    forward.
Qed.

Lemma read_sum_eq : forall n lc, read_sum n lc ≈
  if zlt n 1000 then
    let nums := map (fun c => Int.unsigned c - char0) lc in
    b <- for_loop 0 4 (read_sum_inner n nums) ;; if (b : bool) then Ret tt else
    lc' <- read_list 4;; read_sum (n + sum_Z nums) lc'
  else Ret tt.
Proof.
  intros.
  unfold read_sum.
  rewrite unfold_aloop.
  if_tac; [|reflexivity].
  unfold ITree._aloop, id.
  rewrite bind_bind.
  apply eutt_bind; [|reflexivity].
  intros [].
  - rewrite Shallow.bind_ret, unfold_aloop.
    reflexivity.
  - rewrite bind_bind.
    apply eutt_bind; [|reflexivity].
    intro.
    rewrite Shallow.bind_ret; reflexivity.
Qed.

Lemma for_loop_eq : forall i z body,
  for_loop i z body ≈ if i <? z then b <- body i ;; if (b : bool) then Ret true else for_loop (i + 1) z body else Ret false.
Proof.
  intros.
  unfold for_loop.
  rewrite unfold_aloop.
  simple_if_tac; [|reflexivity].
  unfold ITree._aloop, id.
  rewrite bind_bind.
  apply eutt_bind; [|reflexivity].
  intros [].
  - rewrite Shallow.bind_ret, unfold_aloop.
    reflexivity.
  - rewrite Shallow.bind_ret; reflexivity.
Qed.

Lemma sum_Z_app : forall l1 l2, sum_Z (l1 ++ l2) = sum_Z l1 + sum_Z l2.
Proof.
  induction l1; auto; simpl; intros.
  rewrite IHl1; omega.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  replace_SEP 0 (ITREE main_itree).
  { go_lower; apply has_ext_ITREE. }
  forward.
  rewrite <- (emp_sepcon (ITREE main_itree)); Intros.
  replace_SEP 0 (mem_mgr gv).
  { go_lower; apply create_mem_mgr. }
  forward_call (tarray tuchar 4, gv).
  { simpl; repeat (split; auto); rep_omega. }
  Intro buf.
  forward_if (buf <> nullval).
  { if_tac; entailer!. }
  { forward_call 1.
    rep_omega.
    entailer!. }
  { forward.
    entailer!. }
  Intros; rewrite if_false by auto.
  unfold main_itree.
  forward_call (Ews, buf, 4, fun lc => read_sum 0 lc).
  { simpl; cancel. }
  Intros lc.
  set (Inv := EX n : Z, EX lc : list int,
    PROP (0 <= n < 1040; Forall (fun i => Int.unsigned i <= Byte.max_unsigned) lc)
    LOCAL (temp _i (Vint (Int.repr 4)); temp _buf buf; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (ITREE (read_sum n lc); data_at Ews (tarray tuchar 4) (map Vint lc) buf;
      mem_mgr gv; malloc_token Ews (tarray tuchar 4) buf)).
  forward_while Inv.
  { Exists 0 lc; entailer!. }
  { entailer!. }
  - clear dependent lc; rename lc0 into lc.
    erewrite ITREE_ext by apply read_sum_eq.
    rewrite if_true by auto; simpl ITREE.
    set (nums := map (fun i => Int.unsigned i - char0) lc).
    assert_PROP (Zlength lc = 4).
    { entailer!.
      rewrite Zlength_map in *; auto. }
    assert (Zlength nums = 4) by (subst nums; rewrite Zlength_map; auto).
    forward_for_simple_bound 4 (EX j : Z, PROP (0 <= n + sum_Z (sublist 0 j nums) < 1000 + 10 * j)
     LOCAL (temp _i (Vint (Int.repr 4)); temp _buf buf; temp _n (Vint (Int.repr (n + sum_Z (sublist 0 j nums)))); gvars gv)
     SEP (ITREE (b <- for_loop j 4
         (read_sum_inner n nums) ;; if (b : bool) then Ret tt else lc' <- read_list 4 ;; read_sum (n + sum_Z nums) lc');
             data_at Ews (tarray tuchar 4) (map Vint lc) buf; mem_mgr gv; malloc_token Ews (tarray tuchar 4) buf)).
    + entailer!.
      { omega. }
    + simpl.
      forward.
      { entailer!.
        rewrite zero_ext_inrange by (apply Forall_Znth; auto; omega).
        apply Forall_Znth; auto; omega. }
      forward.
      rewrite zero_ext_inrange by (apply Forall_Znth; auto; omega).
      forward_if (0 <= Int.unsigned (Znth i lc) - char0 < 10).
      { forward_call (tarray tuchar 4, buf, gv).
        { rewrite if_false by auto; cancel. }
        forward.
        entailer!.
        apply ITREE_impl.
        rewrite for_loop_eq.
        destruct (Z.ltb_spec i 4); try omega.
        unfold read_sum_inner at 2.
        replace (_ || _)%bool with true.
        rewrite !Shallow.bind_ret; reflexivity.
        symmetry; rewrite orb_true_iff.
        rewrite Int.unsigned_sub_borrow in *.
        unfold Int.sub_borrow in *.
        subst nums; rewrite Znth_map by omega.
        rewrite (Int.unsigned_repr 48), Int.unsigned_zero, Z.sub_0_r in * by rep_omega.
        destruct (zlt _ _); [right; apply Z.ltb_lt | left; apply Z.leb_le]; auto.
        rewrite Int.unsigned_zero in *; simpl in *.
        unfold char0; omega. }
      { forward.
        entailer!.
        unfold Int.sub in *.
        rewrite Int.unsigned_repr_eq, Int.unsigned_repr in * by computable.
        pose proof (Int.unsigned_range (Znth i lc)).
        destruct (zlt (Int.unsigned (Znth i lc)) char0).
        { unfold char0 in *; rewrite <- Z_mod_plus_full with (b := 1), Zmod_small in *; rep_omega. }
        unfold char0 in *; rewrite Zmod_small in *; omega. }
      unfold Int.sub.
      rewrite Int.unsigned_repr by computable.
      forward.
      rewrite add_repr.
      erewrite ITREE_ext by (rewrite for_loop_eq; reflexivity).
      destruct (Z.ltb_spec i 4); try omega.
      unfold read_sum_inner at 2.
      unfold nums; rewrite Znth_map by omega.
      assert (((10 <=? Int.unsigned (Znth i lc) - char0) || (Int.unsigned (Znth i lc) - char0 <? 0))%bool = false) as Hin.
      { rewrite orb_false_iff.
        split; [apply Z.leb_nle | apply Z.ltb_nlt]; omega. }
      rewrite Hin.
      assert (sublist 0 (i + 1) nums = sublist 0 i nums ++ [Int.unsigned (Znth i lc) - char0]) as Hi.
      { rewrite (sublist_split _ i (i + 1)), (sublist_one i (i + 1)) by omega.
        f_equal; subst nums.
        rewrite Znth_map by omega; auto. }
      forward_call (gv, n + sum_Z (sublist 0 (i + 1) nums),
        b <- for_loop (i + 1) 4 (read_sum_inner n nums) ;; if (b : bool) then Ret tt else lc' <- read_list 4 ;; read_sum (n + sum_Z nums) lc').
      { entailer!.
        rewrite Hi, sum_Z_app; simpl.
        rewrite Z.add_assoc, Z.add_0_r; auto. }
      { rewrite sepcon_assoc; apply sepcon_derives; cancel.
        apply ITREE_impl; rewrite !bind_bind.
        apply eutt_bind; [|reflexivity].
        intros [].
        rewrite Shallow.bind_ret; reflexivity. }
      { rewrite Hi, sum_Z_app; simpl; omega. }
      entailer!.
      { rewrite Hi, sum_Z_app; simpl.
        rewrite Z.add_0_r, Z.add_assoc; split; auto; omega. }
    + erewrite ITREE_ext by (rewrite for_loop_eq; reflexivity).
      destruct (Z.ltb_spec 4 4); try omega.
      forward_call (Ews, buf, 4, fun lc' => read_sum (n + sum_Z nums) lc').
      { rewrite sepcon_assoc; apply sepcon_derives; cancel.
        apply ITREE_impl.
        simpl; rewrite Shallow.bind_ret; reflexivity. }
      Intros lc'.
      forward.
      rewrite sublist_same in * by auto.
      Exists (n + sum_Z nums, lc'); entailer!.
      apply derives_refl.
  - subst Inv.
    forward_call (tarray tuchar 4, buf, gv).
    { rewrite if_false by auto; cancel. }
    forward.
    cancel; apply ITREE_impl.
    rewrite read_sum_eq.
    rewrite if_false; [reflexivity | omega].
Qed.

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec ext_link.

Lemma prog_correct:
  semax_prog_ext prog main_itree Vprog Gprog.
Proof.
prove_semax_prog.
(*semax_func_cons_ext.
{ simpl; Intro i.
  apply typecheck_return_value; auto. }
semax_func_cons_ext.
semax_func_cons body_print_intr.
semax_func_cons body_print_int.
semax_func_cons body_main.
Qed.*)
Admitted.

Require Import VST.veric.SequentialClight.
Require Import VST.progs.io_mem_dry.

Definition init_mem_exists : { m | Genv.init_mem prog = Some m }.
Proof.
  unfold Genv.init_mem; simpl.
Admitted. (* seems true, but hard to prove -- can we compute it? *)

Definition init_mem := proj1_sig init_mem_exists.

Definition main_block_exists : {b | Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b}.
Proof.
  eexists; simpl.
  unfold Genv.find_symbol; simpl; reflexivity.
Qed.

Definition main_block := proj1_sig main_block_exists.

Theorem prog_toplevel : exists q : Clight_new.corestate,
  semantics.initial_core (Clight_new.cl_core_sem (globalenv prog)) 0 init_mem q init_mem (Vptr main_block Ptrofs.zero) [] /\
  forall n, @step_lemmas.dry_safeN _ _ _ _ Clight_sim.genv_symb_injective (Clight_sim.coresem_extract_cenv (Clight_new.cl_core_sem (globalenv prog)) (prog_comp_env prog))
             (io_dry_spec ext_link) {| Clight_sim.CC.genv_genv := Genv.globalenv prog; Clight_sim.CC.genv_cenv := prog_comp_env prog |} n
            main_itree q init_mem.
Proof.
  edestruct whole_program_sequential_safety_ext with (V := Vprog) as (b & q & m' & Hb & Hq & Hsafe).
  - apply juicy_dry_specs.
  - apply dry_spec_mem.
  - apply CSHL_Sound.semax_prog_ext_sound, prog_correct.
  - apply (proj2_sig init_mem_exists).
  - exists q.
    rewrite (proj2_sig main_block_exists) in Hb; inv Hb.
    assert (m' = init_mem); [|subst; auto].
    destruct Hq; tauto.
Qed.
