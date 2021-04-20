Require Import VST.progs.io_mem.
Require Import VST.progs.io_mem_specs.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition putchars_spec := DECLARE _putchars putchars_spec.
Definition getchars_spec := DECLARE _getchars getchars_spec.

Lemma div_10_dec : forall n, 0 < n ->
  (Z.to_nat (n / 10) < Z.to_nat n)%nat.
Proof.
  intros.
  change 10 with (Z.of_nat 10).
  rewrite <- (Z2Nat.id n) by lia.
  rewrite <- div_Zdiv by discriminate.
  rewrite !Nat2Z.id.
  apply Nat2Z.inj_lt.
  rewrite div_Zdiv, Z2Nat.id by lia; simpl.
  apply Z.div_lt; auto; lia.
Qed.

Program Fixpoint chars_of_Z (n : Z) { measure (Z.to_nat n) } : list byte :=
  let n' := n / 10 in
  match n' <=? 0 with true => [Byte.repr (n + char0)] | false => chars_of_Z n' ++ [Byte.repr (n mod 10 + char0)] end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous.
  eapply Z.lt_le_trans, Z_mult_div_ge with (b := 10); lia.
Defined.

(* The function computed by print_intr *)
Program Fixpoint intr n { measure (Z.to_nat n) } : list byte :=
  match n <=? 0 with
  | true => []
  | false => intr (n / 10) ++ [Byte.repr (n mod 10 + char0)]
  end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous; lia.
Defined.

Definition replace_list {X} i (l : list X) (l' : list X) :=
  sublist 0 i l ++ l' ++ sublist (i + Zlength l') (Zlength l) l.

Definition print_intr_spec :=
 DECLARE _print_intr
  WITH sh : share, i : Z, buf : val, contents : list val
  PRE [ tuint, tptr tuchar ]
    PROP (writable_share sh; 0 <= i <= Int.max_unsigned; Zlength (intr i) <= Zlength contents <= Int.max_signed)
    PARAMS (Vint (Int.repr i); buf)
    GLOBALS ()
    SEP (data_at sh (tarray tuchar (Zlength contents)) contents buf)
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Zlength (intr i)))))
    SEP (data_at sh (tarray tuchar (Zlength contents)) (replace_list 0 contents (map Vubyte (intr i))) buf).

Definition print_int_spec :=
 DECLARE _print_int
  WITH gv : globals, i : Z, tr : IO_itree
  PRE [ tuint ]
    PROP (0 <= i < 10000)
    PARAMS (Vint (Int.repr i))
    GLOBALS (gv)
    SEP (mem_mgr gv; ITREE (write_list stdout (chars_of_Z i ++ [Byte.repr newline]) ;; tr))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; ITREE tr).

Definition for_loop {file_id} i z (body : Z -> itree (@IO_event file_id) bool) :=
  ITree.iter (fun '(b, j) => if (b : bool) then Ret (inr true) else if j <? z then b <- body j ;; Ret (inl (b, j + 1)) else Ret (inr false)) (false, i).

Definition sum_Z l := fold_right Z.add 0 l.

Definition read_sum_inner n nums j :=
  if orb (10 <=? Znth j nums) (Znth j nums <? 0) then Ret true
  else write_list stdout (chars_of_Z (n + sum_Z (sublist 0 (j + 1) nums)) ++ [Byte.repr newline]);; Ret false.

Definition read_sum n lc : IO_itree :=
  ITree.iter (fun '(b, n, lc) => if (b : bool) then Ret (inr tt) else
  if zlt n 1000 then
    let nums := map (fun c => Byte.unsigned c - char0) lc in
    b <- for_loop 0 4 (read_sum_inner n nums) ;; if (b : bool) then Ret (inl (true, n, lc)) else
    lc' <- read_list stdin 4;; Ret (inl (false, n + sum_Z nums, lc'))
  else Ret (inr tt)) (false, n, lc).

Definition main_itree := lc <- read_list stdin 4;; read_sum 0 lc.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog main_itree gv
  POST [ tint ] PROP () LOCAL () SEP (mem_mgr gv; ITREE (Ret tt : @IO_itree (@IO_event nat))).

Definition Gprog : funspecs := ltac:(with_library prog [putchars_spec; getchars_spec;
  print_intr_spec; print_int_spec; main_spec]).

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
  | false => intr (n / 10) ++ [Byte.repr (n mod 10 + char0)]
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
  assert (p * z1 + p <= p * z); try lia.
  rewrite <- Z.mul_succ_r.
  apply Zmult_le_compat_l; lia.
Qed.

Lemma intr_lt : forall n, 0 < n -> Zlength (intr (n / 10)) = Zlength (intr n) - 1.
Proof.
  intros.
  rewrite (intr_eq n).
  destruct (n <=? 0) eqn: Hn.
  { apply Zle_bool_imp_le in Hn; lia. }
  rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma replace_list_nil : forall {X} i (l : list X), 0 <= i <= Zlength l -> replace_list i l [] = l.
Proof.
  intros; unfold replace_list.
  rewrite Zlength_nil, Z.add_0_r; simpl.
  rewrite sublist_rejoin, sublist_same by lia; auto.
Qed.

Lemma replace_list_upd_snoc : forall {X} i (l l' : list X) x, 0 <= i -> i + Zlength l' < Zlength l ->
  upd_Znth (i + Zlength l') (replace_list i l l') x = replace_list i l (l' ++ [x]).
Proof.
  intros; unfold replace_list.
  rewrite upd_Znth_app2; rewrite ?Zlength_sublist; try rep_lia.
  f_equal.
  rewrite Z.sub_0_r, Z.add_simpl_l, upd_Znth_app2; rewrite ?Zlength_sublist; try rep_lia.
  rewrite Zminus_diag, Zlength_app, Zlength_cons, Zlength_nil, upd_Znth0_old, <- app_assoc; simpl; f_equal; f_equal.
  rewrite Zlength_sublist by rep_lia.
  rewrite sublist_sublist by rep_lia.
  f_equal; lia.
  { rewrite Zlength_sublist; rep_lia. }
  { rewrite Zlength_app, Zlength_sublist; rep_lia. }
Qed.

Lemma body_print_intr: semax_body Vprog Gprog f_print_intr print_intr_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP ()
    LOCAL (temp _k (Vint (Int.repr (Zlength (intr i) - 1))))
    SEP (data_at sh (tarray tuchar (Zlength contents)) (replace_list 0 contents (map Vubyte (intr i))) buf)).
  - forward.
    rewrite divu_repr by rep_lia.
    forward.
    forward_call (sh, i / 10, buf, contents).
    { rewrite intr_lt by lia; split; auto; try lia.
      assert (i / 10 < i).
      { apply Z.div_lt; lia. }
       split.
      apply Z.div_pos; lia. 
      rep_lia.
    }
    rewrite modu_repr by (lia || computable).
    assert (repable_signed (Zlength (intr (i / 10)))).
    { split; try rep_lia.
      rewrite intr_lt; try lia. }
    forward.
    { entailer!.
      split; try rep_lia.
      rewrite intr_lt; try lia. }
    entailer!.
    { rewrite intr_lt by lia; auto. }
    rewrite (intr_eq i).
    destruct (i <=? 0) eqn: Hi; [apply Zle_bool_imp_le in Hi; lia|].
    pose proof (Z_mod_lt i 10).
    rewrite <- (Zlength_map _ _ Vubyte), <- (Z.add_0_l (Zlength (map _ _))), replace_list_upd_snoc.
    rewrite (zero_ext_inrange 8 (Int.repr (i mod 10))), add_repr.
    rewrite zero_ext_inrange, map_app.
    unfold Vubyte at 3; simpl.
    rewrite Byte.unsigned_repr by (unfold char0; rep_lia); apply derives_refl.
    { rewrite Int.unsigned_repr; simpl; rep_lia. }
    { rewrite Int.unsigned_repr; simpl; rep_lia. }
    { lia. }
    { rewrite Zlength_map, intr_lt; rep_lia. }
  - forward.
    entailer!.
    rewrite replace_list_nil by rep_lia; auto.
  - forward.
    rewrite Z.sub_simpl_r; entailer!.
Qed.

Lemma chars_of_Z_eq : forall n, chars_of_Z n =
  let n' := n / 10 in
  match n' <=? 0 with true => [Byte.repr (n + char0)] | false => chars_of_Z n' ++ [Byte.repr (n mod 10 + char0)] end.
Proof.
  intros.
  unfold chars_of_Z at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold chars_of_Z.
  destruct (_ <=? _); reflexivity.
Qed.

Lemma chars_of_Z_intr : forall n,
  chars_of_Z n = if n <=? 0 then [Byte.repr (n + char0)] else intr n.
Proof.
  intros.
  destruct (Z.leb_spec n 0).
  { rewrite chars_of_Z_eq; simpl.
    apply Zdiv_le_compat_r with (p := 10) in H; try lia.
    rewrite Zdiv_0_l in H.
    destruct (Z.leb_spec (n / 10) 0); auto; lia. }
  induction n as [? IH] using (well_founded_induction (Zwf.Zwf_well_founded 0)).
  rewrite chars_of_Z_eq, intr_eq.
  destruct (n <=? 0) eqn: Hn; [apply Zle_bool_imp_le in Hn; lia|].
  simpl.
  destruct (n / 10 <=? 0) eqn: Hdiv.
  - apply Zle_bool_imp_le in Hdiv.
    assert (0 <= n / 10).
    { apply Z.div_pos; lia. }
    assert (n / 10 = 0) as Hz by lia.
    rewrite Hz; simpl.
    apply Z.div_small_iff in Hz as [|]; try lia.
    rewrite Zmod_small; auto.
  - apply Z.leb_nle in Hdiv.
    rewrite IH; auto; try lia.
    split; try lia.
    apply Z.div_lt; auto; lia.
Qed.

Lemma intr_length : forall n a, 0 <= a -> n < Z.pow 10 a -> Zlength (intr n) <= a.
Proof.
  induction n using (well_founded_induction (Zwf.Zwf_well_founded 0)); intros.
  rewrite intr_eq.
  destruct (Z.leb_spec n 0); [rewrite Zlength_nil; lia|].
  rewrite Zlength_app.
  assert (Zlength (intr (n / 10)) <= a - 1); [|rewrite Zlength_cons, Zlength_nil; lia].
  assert (0 <= a - 1).
  { destruct (Z.eq_dec a 0); subst; simpl in *; lia. }
  apply H; auto.
  - split; try lia.
    apply Z.div_lt; auto; lia.
  - apply Zmult_lt_reg_r with 10; try lia.
    rewrite (Z.mul_comm (10 ^ _)), <- Z.pow_succ_r by auto.
    unfold Z.succ; rewrite Z.sub_simpl_r.
    eapply Z.le_lt_trans; eauto.
    rewrite Z.mul_comm; apply Z.mul_div_le; lia.
Qed.

Lemma chars_of_Z_length : forall n a, 0 < a -> n < Z.pow 10 a -> Zlength (chars_of_Z n) <= a.
Proof.
  intros.
  rewrite chars_of_Z_intr.
  destruct (Z.leb_spec n 0); [|apply intr_length; lia].
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma body_print_int: semax_body Vprog Gprog f_print_int print_int_spec.
Proof.
  start_function.
  forward_call (tarray tuchar 5, gv).
  { split; auto; simpl; computable. }
  Intro buf.
  forward_if (buf <> nullval).
  { if_tac; entailer!. }
  { forward_call 1; contradiction. }
  { forward.
    entailer!. }
  Intros; rewrite if_false by auto.
  forward_if (PROP ()
    LOCAL (temp _buf buf; gvars gv; temp _i (Vint (Int.repr i));
                 temp _k (Vint (Int.repr (Zlength (chars_of_Z i ++ [Byte.repr newline])))))
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar 5) buf;
            data_at Ews (tarray tuchar 5) (map Vubyte (chars_of_Z i) ++ Vubyte (Byte.repr newline) ::
              repeat Vundef (Z.to_nat (4 - Zlength (chars_of_Z i)))) buf;
            ITREE (write_list stdout (chars_of_Z i ++ [Byte.repr newline]);; tr))).
  - Intros.
    forward.
    forward.
    forward.
    entailer!.
  - Intros.
    sep_apply data_at__data_at.
    unfold default_val; simpl.
    assert (Zlength (intr i) <= 4).
    { apply intr_length; try lia. }
    forward_call (Ews, i, buf, [Vundef; Vundef; Vundef; Vundef; Vundef]).
    { rewrite !Zlength_cons, Zlength_nil.
      simpl; repeat (split; auto); rep_lia. }
    forward.
    { entailer!.
      rewrite !Zlength_cons, Zlength_nil; rep_lia. }
    forward.
    entailer!.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil, chars_of_Z_intr.
      destruct (Z.leb_spec i 0); auto; lia. }
    unfold replace_list; simpl.
    rewrite (sublist_repeat _ _ 5 Vundef).
    rewrite !Zlength_cons, Zlength_nil, Zlength_map; simpl.
    rewrite upd_Znth_app2.
    rewrite Zlength_map, Zminus_diag, upd_Znth0_old, sublist_repeat; try lia.
    apply derives_refl'.
    f_equal.
    rewrite chars_of_Z_intr.
    destruct (Z.leb_spec i 0); try lia.
    rewrite zero_ext_inrange.
    f_equal; f_equal; f_equal; f_equal.
    rewrite Zlength_repeat; try lia.
    { simpl; rewrite Int.unsigned_repr; rep_lia. }
    { rewrite Zlength_repeat; lia. }
    { rewrite Zlength_repeat; lia. }
    { rewrite Zlength_map, Zlength_repeat; lia. }
    { rewrite Zlength_map; rep_lia. }
    { rewrite !Zlength_cons, Zlength_nil, Zlength_map; lia. }
  - forward_call (Ews, buf, chars_of_Z i ++ [Byte.repr newline],
      5, repeat Vundef (Z.to_nat (4 - Zlength (chars_of_Z i))), tr).
    { rewrite map_app, <- app_assoc; simpl; cancel. }
    forward_call (tarray tuchar 5, buf, gv).
    { rewrite if_false by auto; cancel. }
    forward.
Qed.

Lemma read_sum_eq : forall n lc, read_sum n lc ≈
  if zlt n 1000 then
    let nums := map (fun c => Byte.unsigned c - char0) lc in
    b <- for_loop 0 4 (read_sum_inner n nums) ;; if (b : bool) then Ret tt else
    lc' <- read_list stdin 4;; read_sum (n + sum_Z nums) lc'
  else Ret tt.
Proof.
  intros.
  unfold read_sum.
  rewrite unfold_iter.
  if_tac; [|rewrite bind_ret_l; reflexivity].
  rewrite bind_bind.
  apply eqit_bind; [|reflexivity].
  intros [].
  - rewrite bind_ret_l, tau_eutt.
    rewrite unfold_iter.
    rewrite bind_ret_l; reflexivity.
  - rewrite bind_bind.
    apply eqit_bind; [|reflexivity].
    intro.
    rewrite bind_ret_l, tau_eutt; reflexivity.
Qed.

Lemma for_loop_eq : forall {file_id} i z body,
  @for_loop file_id i z body ≈ if i <? z then b <- body i ;; if (b : bool) then Ret true else for_loop (i + 1) z body else Ret false.
Proof.
  intros.
  unfold for_loop.
  rewrite unfold_iter.
  simple_if_tac; [|rewrite bind_ret_l; reflexivity].
  rewrite bind_bind.
  apply eqit_bind; [|reflexivity].
  intros [].
  - rewrite bind_ret_l, tau_eutt, unfold_iter.
    rewrite bind_ret_l; reflexivity.
  - rewrite bind_ret_l, tau_eutt; reflexivity.
Qed.

Lemma sum_Z_app : forall l1 l2, sum_Z (l1 ++ l2) = sum_Z l1 + sum_Z l2.
Proof.
  induction l1; auto; simpl; intros.
  rewrite IHl1; lia.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (has_ext_ITREE(E := @IO_event nat)).
  rewrite <- (emp_sepcon (ITREE _)); Intros.
  replace_SEP 0 (mem_mgr gv) by (go_lower; apply create_mem_mgr).
  forward.
  forward_call (tarray tuchar 4, gv).
  { simpl; repeat (split; auto); rep_lia. }
  Intro buf.
  forward_if (buf <> nullval).
  { if_tac; entailer!. }
  { forward_call 1; contradiction. }
  { forward.
    entailer!. }
  Intros; rewrite if_false by auto.
  unfold main_itree.
  forward_call (Ews, buf, 4, fun lc => read_sum 0 lc).
  { simpl; cancel. }
  Intros lc.
  set (Inv := EX n : Z, EX lc : list byte,
    PROP (0 <= n < 1040)
    LOCAL (temp _i (Vint (Int.repr 4)); temp _buf buf; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (ITREE (read_sum n lc); data_at Ews (tarray tuchar 4) (map Vubyte lc) buf;
      mem_mgr gv; malloc_token Ews (tarray tuchar 4) buf)).
  forward_while Inv.
  { Exists 0 lc; entailer!. }
  { entailer!. }
  - clear dependent lc; rename lc0 into lc.
    rewrite read_sum_eq.
    rewrite if_true by auto; simpl ITREE.
    set (nums := map (fun i => Byte.unsigned i - char0) lc).
    assert_PROP (Zlength lc = 4).
    { entailer!.
      rewrite Zlength_map in *; auto. }
    assert (Zlength nums = 4) by (subst nums; rewrite Zlength_map; auto).
    forward_for_simple_bound 4 (EX j : Z, PROP (0 <= n + sum_Z (sublist 0 j nums) < 1000 + 10 * j)
     LOCAL (temp _i (Vint (Int.repr 4)); temp _buf buf; temp _n (Vint (Int.repr (n + sum_Z (sublist 0 j nums)))); gvars gv)
     SEP (ITREE (b <- for_loop j 4
         (read_sum_inner n nums) ;; if (b : bool) then Ret tt else lc' <- read_list stdin 4 ;; read_sum (n + sum_Z nums) lc');
             data_at Ews (tarray tuchar 4) (map Vubyte lc) buf; mem_mgr gv; malloc_token Ews (tarray tuchar 4) buf)).
    + entailer!.
      { lia. }
    + simpl.
      forward.
      { entailer!.
        unfold Vubyte; simpl.
        rewrite Int.unsigned_repr; rep_lia. }
      forward.
      rewrite Znth_map by lia; simpl.
      rewrite zero_ext_inrange.
      forward.
      unfold Int.sub.
      rewrite !Int.unsigned_repr by rep_lia.
      forward_if (0 <= Byte.unsigned (Znth i lc) - char0 < 10).
      { forward_call (tarray tuchar 4, buf, gv).
        { rewrite if_false by auto; cancel. }
        forward.
        entailer!.
        rewrite for_loop_eq.
        destruct (Z.ltb_spec i 4); try lia.
        unfold read_sum_inner at 2.
        replace (_ || _)%bool with true.
        rewrite !bind_ret_l; auto.
        { symmetry; rewrite orb_true_iff.
          subst nums; rewrite Znth_map by lia.
          destruct (Z.ltb_spec (Byte.unsigned (Znth i lc) - char0) 0); auto.
          rewrite Int.unsigned_repr in * by (unfold char0 in *; rep_lia).
          left; apply Z.leb_le; unfold char0 in *; lia. } }
      { forward.
        entailer!.
        rewrite Int.unsigned_repr_eq in *.
        destruct (zlt (Byte.unsigned (Znth i lc)) char0).
        { unfold char0 in *; rewrite <- Z_mod_plus_full with (b := 1), Zmod_small in *; rep_lia. }
        unfold char0 in *; rewrite Zmod_small in *; rep_lia. }
      forward.
      rewrite add_repr.
      rewrite for_loop_eq.
      destruct (Z.ltb_spec i 4); try lia.
      unfold read_sum_inner at 2.
      unfold nums; rewrite Znth_map by lia.
      assert (((10 <=? Byte.unsigned (Znth i lc) - char0) || (Byte.unsigned (Znth i lc) - char0 <? 0))%bool = false) as Hin.
      { rewrite orb_false_iff.
        split; [apply Z.leb_nle | apply Z.ltb_nlt]; lia. }
      rewrite Hin.
      assert (sublist 0 (i + 1) nums = sublist 0 i nums ++ [Byte.unsigned (Znth i lc) - char0]) as Hi.
      { rewrite (sublist_split _ i (i + 1)), (sublist_one i (i + 1)) by lia.
        f_equal; subst nums.
        rewrite Znth_map by lia; auto. }
      forward_call (gv, n + sum_Z (sublist 0 (i + 1) nums),
        b <- for_loop (i + 1) 4 (read_sum_inner n nums) ;; if (b : bool) then Ret tt else lc' <- read_list stdin 4 ;; read_sum (n + sum_Z nums) lc').
      { entailer!.
        rewrite Hi, sum_Z_app; simpl.
        rewrite Z.add_assoc, Z.add_0_r; auto. }
      { rewrite sepcon_assoc; apply sepcon_derives; cancel.
        rewrite !bind_bind.
        apply ITREE_impl.
        apply eqit_bind; [|reflexivity].
        intros [].
        rewrite bind_ret_l; reflexivity. }
      { rewrite Hi, sum_Z_app; simpl; lia. }
      entailer!.
      { rewrite Hi, sum_Z_app; simpl.
        rewrite Z.add_0_r, Z.add_assoc; split; auto; lia. }
      { rewrite Int.unsigned_repr by rep_lia.
        pose proof (Byte.unsigned_range (Znth i lc)) as [_ Hmax].
        unfold Byte.modulus, two_power_nat in Hmax; simpl in *; lia. }
    + rewrite for_loop_eq.
      destruct (Z.ltb_spec 4 4); try lia.
      forward_call (Ews, buf, 4, fun lc' => read_sum (n + sum_Z nums) lc').
      { rewrite sepcon_assoc; apply sepcon_derives; cancel.
        simpl; rewrite bind_ret_l; auto. }
      Intros lc'.
      forward.
      rewrite sublist_same in * by auto.
      Exists (n + sum_Z nums, lc'); entailer!.
      apply derives_refl.
  - subst Inv.
    forward_call (tarray tuchar 4, buf, gv).
    { rewrite if_false by auto; cancel. }
    forward.
    cancel.
    rewrite read_sum_eq.
    rewrite if_false; [auto | lia].
Qed.

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec ext_link.

Lemma prog_correct:
  semax_prog prog main_itree Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_exit.
semax_func_cons body_free.
semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
semax_func_cons_ext.
{ simpl; Intro msg.
  apply typecheck_return_value with (t := Tint16signed); auto. }
semax_func_cons_ext.
semax_func_cons body_print_intr.
semax_func_cons body_print_int.
semax_func_cons body_main.
Qed.

Require Import VST.veric.SequentialClight.
Require Import VST.progs.io_mem_dry.

Definition init_mem_exists : { m | Genv.init_mem prog = Some m }.
Proof.
  unfold Genv.init_mem; simpl.
Ltac alloc_block m n := match n with
  | O => idtac
  | S ?n' => let m' := fresh "m" in let Hm' := fresh "Hm" in
    destruct (dry_mem_lemmas.drop_alloc m) as [m' Hm']; alloc_block m' n'
  end.
  alloc_block Mem.empty 60%nat.
  eexists; repeat match goal with H : ?a = _ |- match ?a with Some m' => _ | None => None end = _ => rewrite H end.
  reflexivity.
Qed.

Definition init_mem := proj1_sig init_mem_exists.

Definition main_block_exists : {b | Genv.find_symbol (Genv.globalenv prog) (AST.prog_main prog) = Some b}.
Proof.
  eexists; simpl.
  unfold Genv.find_symbol; simpl; reflexivity.
Qed.

Definition main_block := proj1_sig main_block_exists.

Theorem prog_toplevel : exists q,
  semantics.initial_core (Clight_core.cl_core_sem (globalenv prog)) 0 init_mem q init_mem (Vptr main_block Ptrofs.zero) [] /\
  forall n, @step_lemmas.dry_safeN _ _ _ _ semax.genv_symb_injective (Clight_core.cl_core_sem (globalenv prog))
             (io_dry_spec ext_link) {| genv_genv := Genv.globalenv prog; genv_cenv := prog_comp_env prog |} n
            main_itree q init_mem.
Proof.
  edestruct whole_program_sequential_safety_ext with (V := Vprog) as (b & q & Hb & Hq & Hsafe).
  - repeat intro; simpl. apply I.
  - apply juicy_dry_specs.
  - apply dry_spec_mem.
  - apply CSHL_Sound.semax_prog_sound, prog_correct.
  - apply (proj2_sig init_mem_exists).
  - exists q.
    rewrite (proj2_sig main_block_exists) in Hb; inv Hb.
    auto.
Qed.
